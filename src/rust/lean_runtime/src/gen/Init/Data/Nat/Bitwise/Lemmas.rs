// Lean compiler output
// Module: Init.Data.Nat.Bitwise.Lemmas
// Imports: Init.Data.Nat.Bitwise.Basic Init.BinderPredicates Init.Data.Bool Init.Data.Nat.Log2 Init.ByCases Init.Data.Int.Pow Init.Data.Nat.Lemmas Init.Omega Init.RCases Init.TacticsExtra
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Log2::{
    initialize_Init_Data_Nat_Log2, runtime_initialize_Init_Data_Nat_Log2,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::lean_imports_rs::Init::Prelude::lean_array_push;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
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
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__5_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
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
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__7_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__9_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__10_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0],
};
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__11_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__10_value)
            as *mut crate::leanh::LeanObject,
        3294379458557754569 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_bitwise__div__two__pow___auto__9___closed__12_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 102, 108, 0],
};
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_bitwise__div__two__pow___auto__9___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_bitwise__div__two__pow___auto__9___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_bitwise__div__two__pow___auto__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_bitwise__mod__two__pow___auto__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_bitwise__mul__two__pow___auto__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_shiftLeft__bitwise__distrib___auto__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Nat_shiftRight__bitwise__distrib___auto__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_90_ = l_Nat_bitwise__div__two__pow___auto__9___closed__12;
    v___x_91_ = l_Lean_mkAtom(v___x_90_);
    return v___x_91_;
}
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_92_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__13),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__13_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__13,
    );
    v___x_93_ = l_Nat_bitwise__div__two__pow___auto__9___closed__5;
    v___x_94_ = lean_array_push(v___x_93_, v___x_92_);
    return v___x_94_;
}
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_95_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__14),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__14_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__14,
    );
    v___x_96_ = l_Nat_bitwise__div__two__pow___auto__9___closed__11;
    v___x_97_ = crate::leanh::lean_box(2);
    v___x_98_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_98_, 0, v___x_97_);
    crate::leanh::lean_ctor_set(v___x_98_, 1, v___x_96_);
    crate::leanh::lean_ctor_set(v___x_98_, 2, v___x_95_);
    return v___x_98_;
}
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_99_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__15),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__15_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__15,
    );
    v___x_100_ = l_Nat_bitwise__div__two__pow___auto__9___closed__5;
    v___x_101_ = lean_array_push(v___x_100_, v___x_99_);
    return v___x_101_;
}
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_102_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__16),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__16_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__16,
    );
    v___x_103_ = l_Nat_bitwise__div__two__pow___auto__9___closed__9;
    v___x_104_ = crate::leanh::lean_box(2);
    v___x_105_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_105_, 0, v___x_104_);
    crate::leanh::lean_ctor_set(v___x_105_, 1, v___x_103_);
    crate::leanh::lean_ctor_set(v___x_105_, 2, v___x_102_);
    return v___x_105_;
}
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_106_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__17),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__17_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__17,
    );
    v___x_107_ = l_Nat_bitwise__div__two__pow___auto__9___closed__5;
    v___x_108_ = lean_array_push(v___x_107_, v___x_106_);
    return v___x_108_;
}
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_109_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__18),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__18_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__18,
    );
    v___x_110_ = l_Nat_bitwise__div__two__pow___auto__9___closed__7;
    v___x_111_ = crate::leanh::lean_box(2);
    v___x_112_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_112_, 0, v___x_111_);
    crate::leanh::lean_ctor_set(v___x_112_, 1, v___x_110_);
    crate::leanh::lean_ctor_set(v___x_112_, 2, v___x_109_);
    return v___x_112_;
}
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_113_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__19),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__19_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__19,
    );
    v___x_114_ = l_Nat_bitwise__div__two__pow___auto__9___closed__5;
    v___x_115_ = lean_array_push(v___x_114_, v___x_113_);
    return v___x_115_;
}
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_116_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__20),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__20_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__20,
    );
    v___x_117_ = l_Nat_bitwise__div__two__pow___auto__9___closed__4;
    v___x_118_ = crate::leanh::lean_box(2);
    v___x_119_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_119_, 0, v___x_118_);
    crate::leanh::lean_ctor_set(v___x_119_, 1, v___x_117_);
    crate::leanh::lean_ctor_set(v___x_119_, 2, v___x_116_);
    return v___x_119_;
}
pub unsafe fn _init_l_Nat_bitwise__div__two__pow___auto__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_120_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__21,
    );
    return v___x_120_;
}
pub unsafe fn _init_l_Nat_bitwise__mod__two__pow___auto__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_121_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__21,
    );
    return v___x_121_;
}
pub unsafe fn _init_l_Nat_bitwise__mul__two__pow___auto__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_122_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__21,
    );
    return v___x_122_;
}
pub unsafe fn _init_l_Nat_shiftLeft__bitwise__distrib___auto__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_123_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__21,
    );
    return v___x_123_;
}
pub unsafe fn _init_l_Nat_shiftRight__bitwise__distrib___auto__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_124_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21),
        core::ptr::addr_of_mut!(l_Nat_bitwise__div__two__pow___auto__9___closed__21_once),
        _init_l_Nat_bitwise__div__two__pow___auto__9___closed__21,
    );
    return v___x_124_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
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
    res = runtime_initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Bitwise_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Nat_bitwise__div__two__pow___auto__9 = _init_l_Nat_bitwise__div__two__pow___auto__9();
    crate::leanh::lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9);
    l_Nat_bitwise__mod__two__pow___auto__9 = _init_l_Nat_bitwise__mod__two__pow___auto__9();
    crate::leanh::lean_mark_persistent(l_Nat_bitwise__mod__two__pow___auto__9);
    l_Nat_bitwise__mul__two__pow___auto__9 = _init_l_Nat_bitwise__mul__two__pow___auto__9();
    crate::leanh::lean_mark_persistent(l_Nat_bitwise__mul__two__pow___auto__9);
    l_Nat_shiftLeft__bitwise__distrib___auto__5 =
        _init_l_Nat_shiftLeft__bitwise__distrib___auto__5();
    crate::leanh::lean_mark_persistent(l_Nat_shiftLeft__bitwise__distrib___auto__5);
    l_Nat_shiftRight__bitwise__distrib___auto__5 =
        _init_l_Nat_shiftRight__bitwise__distrib___auto__5();
    crate::leanh::lean_mark_persistent(l_Nat_shiftRight__bitwise__distrib___auto__5);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Bitwise_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
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
    res = initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
}
