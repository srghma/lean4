// Lean compiler output
// Module: Init.Control.Lawful.Basic
// Imports: Init.Control.Id Init.Grind.Tactics Init.Ext
use crate::ffi::lean_array_push;
use crate::r#gen::Init::Control::Id::{
    initialize_Init_Control_Id, runtime_initialize_Init_Control_Id,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
pub static l_LawfulMonad_mk_x27___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_LawfulMonad_mk_x27___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_LawfulMonad_mk_x27___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__10_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [105, 110, 116, 114, 111, 115, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_LawfulMonad_mk_x27___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            3278676588586250010 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulMonad_mk_x27___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_LawfulMonad_mk_x27___auto__1___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulMonad_mk_x27___auto__1___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_LawfulMonad_mk_x27___auto__1___closed__18_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [59, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulMonad_mk_x27___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_LawfulMonad_mk_x27___auto__1___closed__21_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_LawfulMonad_mk_x27___auto__1___closed__22_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__21_value)
                as *mut crate::leanh::LeanObject,
            3294379458557754569 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__23_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [114, 102, 108, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulMonad_mk_x27___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_120_ = l_LawfulMonad_mk_x27___auto__1___closed__10;
    v___x_121_ = l_Lean_mkAtom(v___x_120_);
    return v___x_121_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_122_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__12_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__12,
    );
    v___x_123_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_124_ = lean_array_push(v___x_123_, v___x_122_);
    return v___x_124_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_129_ = l_LawfulMonad_mk_x27___auto__1___closed__14;
    v___x_130_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__13_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__13,
    );
    v___x_131_ = lean_array_push(v___x_130_, v___x_129_);
    return v___x_131_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_132_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__15_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__15,
    );
    v___x_133_ = l_LawfulMonad_mk_x27___auto__1___closed__11;
    v___x_134_ = crate::leanh::lean_box(2);
    v___x_135_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_135_, 0, v___x_134_);
    crate::leanh::lean_ctor_set(v___x_135_, 1, v___x_133_);
    crate::leanh::lean_ctor_set(v___x_135_, 2, v___x_132_);
    return v___x_135_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_136_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__16_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__16,
    );
    v___x_137_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_138_ = lean_array_push(v___x_137_, v___x_136_);
    return v___x_138_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_140_ = l_LawfulMonad_mk_x27___auto__1___closed__18;
    v___x_141_ = l_Lean_mkAtom(v___x_140_);
    return v___x_141_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__19_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__19,
    );
    v___x_143_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__17_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__17,
    );
    v___x_144_ = lean_array_push(v___x_143_, v___x_142_);
    return v___x_144_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = l_LawfulMonad_mk_x27___auto__1___closed__23;
    v___x_153_ = l_Lean_mkAtom(v___x_152_);
    return v___x_153_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_154_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__24_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__24,
    );
    v___x_155_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_156_ = lean_array_push(v___x_155_, v___x_154_);
    return v___x_156_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_157_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__25_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__25,
    );
    v___x_158_ = l_LawfulMonad_mk_x27___auto__1___closed__22;
    v___x_159_ = crate::leanh::lean_box(2);
    v___x_160_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_160_, 0, v___x_159_);
    crate::leanh::lean_ctor_set(v___x_160_, 1, v___x_158_);
    crate::leanh::lean_ctor_set(v___x_160_, 2, v___x_157_);
    return v___x_160_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__27() -> *mut crate::leanh::LeanObject {
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_161_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__26_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__26,
    );
    v___x_162_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__20_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__20,
    );
    v___x_163_ = lean_array_push(v___x_162_, v___x_161_);
    return v___x_163_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_164_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__27_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__27,
    );
    v___x_165_ = l_LawfulMonad_mk_x27___auto__1___closed__9;
    v___x_166_ = crate::leanh::lean_box(2);
    v___x_167_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_167_, 0, v___x_166_);
    crate::leanh::lean_ctor_set(v___x_167_, 1, v___x_165_);
    crate::leanh::lean_ctor_set(v___x_167_, 2, v___x_164_);
    return v___x_167_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_168_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__28_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__28,
    );
    v___x_169_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_170_ = lean_array_push(v___x_169_, v___x_168_);
    return v___x_170_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__30() -> *mut crate::leanh::LeanObject {
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_171_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__29_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__29,
    );
    v___x_172_ = l_LawfulMonad_mk_x27___auto__1___closed__7;
    v___x_173_ = crate::leanh::lean_box(2);
    v___x_174_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_174_, 0, v___x_173_);
    crate::leanh::lean_ctor_set(v___x_174_, 1, v___x_172_);
    crate::leanh::lean_ctor_set(v___x_174_, 2, v___x_171_);
    return v___x_174_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__31() -> *mut crate::leanh::LeanObject {
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_175_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__30_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__30,
    );
    v___x_176_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_177_ = lean_array_push(v___x_176_, v___x_175_);
    return v___x_177_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__32() -> *mut crate::leanh::LeanObject {
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_178_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__31_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__31,
    );
    v___x_179_ = l_LawfulMonad_mk_x27___auto__1___closed__4;
    v___x_180_ = crate::leanh::lean_box(2);
    v___x_181_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_181_, 0, v___x_180_);
    crate::leanh::lean_ctor_set(v___x_181_, 1, v___x_179_);
    crate::leanh::lean_ctor_set(v___x_181_, 2, v___x_178_);
    return v___x_181_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_182_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_183_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_183_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_184_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_184_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_185_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_185_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_186_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Lawful_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Lawful_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_LawfulMonad_mk_x27___auto__1 = _init_l_LawfulMonad_mk_x27___auto__1();
    crate::leanh::lean_mark_persistent(l_LawfulMonad_mk_x27___auto__1);
    l_LawfulMonad_mk_x27___auto__3 = _init_l_LawfulMonad_mk_x27___auto__3();
    crate::leanh::lean_mark_persistent(l_LawfulMonad_mk_x27___auto__3);
    l_LawfulMonad_mk_x27___auto__5 = _init_l_LawfulMonad_mk_x27___auto__5();
    crate::leanh::lean_mark_persistent(l_LawfulMonad_mk_x27___auto__5);
    l_LawfulMonad_mk_x27___auto__7 = _init_l_LawfulMonad_mk_x27___auto__7();
    crate::leanh::lean_mark_persistent(l_LawfulMonad_mk_x27___auto__7);
    l_LawfulMonad_mk_x27___auto__9 = _init_l_LawfulMonad_mk_x27___auto__9();
    crate::leanh::lean_mark_persistent(l_LawfulMonad_mk_x27___auto__9);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Lawful_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Lawful_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_Lawful_Basic(builtin);
}
