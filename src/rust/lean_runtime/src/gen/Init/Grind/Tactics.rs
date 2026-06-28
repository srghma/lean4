// Lean compiler output
// Module: Init.Grind.Tactics
// Imports: Init.Core Init.Grind.Interactive
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Grind::Interactive::{
    initialize_Init_Grind_Interactive, l_Lean_Parser_Tactic_Grind_grindSeq,
    l_Lean_Parser_Tactic_grindParam, runtime_initialize_Init_Grind_Interactive,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4};
use crate::r#gen::Init::Tactics::l_Lean_Parser_Tactic_optConfig;
pub static l_Lean_Parser_Tactic_grind___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_grind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Tactic_grind___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Tactic_grind___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__3_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_grind___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grind___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__3_value)
                as *mut crate::leanh::LeanObject,
            7213727686127018646 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__5_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__5_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__3_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__9_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__9_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__11_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [32, 111, 110, 108, 121, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__11_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__15_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [32, 91, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__16_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__17_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__17_value)
                as *mut crate::leanh::LeanObject,
            1164644006045091397 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__19_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__20_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__21_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__25_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__26_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__25_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__26_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__30_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 61, 62, 32, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__31_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__30_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__31_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__33_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__35_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grind: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grindTrace___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [103, 114, 105, 110, 100, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grindTrace___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8341917469546378704 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grindTrace___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [103, 114, 105, 110, 100, 63, 0],
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grindTrace___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grindTrace___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindTrace___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindTrace___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindTrace___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grindTrace: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_sym___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [115, 121, 109, 0],
    };
static mut l_Lean_Parser_Tactic_sym___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_sym___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_sym___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_sym___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_sym___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2698983533533738959 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_sym___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_sym___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_sym___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_sym___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_sym: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_cutsat___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [99, 117, 116, 115, 97, 116, 0],
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_cutsat___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2518545331120607024 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_cutsat___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_cutsat___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_cutsat___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_cutsat: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_lia___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [108, 105, 97, 0],
    };
static mut l_Lean_Parser_Tactic_lia___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_lia___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_lia___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_lia___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_lia___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__0_value)
                as *mut crate::leanh::LeanObject,
            628853965465602645 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_lia___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_lia___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_lia___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_lia___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_lia___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_lia___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_lia___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_lia: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind__order___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [103, 114, 105, 110, 100, 95, 111, 114, 100, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grind__order___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6376312911296474159 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind__order___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind__order___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind__order___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grind__order: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind__linarith___closed__0_value: crate::leanh::LeanStringObject<
    15,
> = crate::leanh::LeanStringObject {
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
        103, 114, 105, 110, 100, 95, 108, 105, 110, 97, 114, 105, 116, 104, 0,
    ],
};
static mut l_Lean_Parser_Tactic_grind__linarith___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_grind__linarith___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6166429773221086783 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind__linarith___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind__linarith___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind__linarith___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grind__linarith: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grobner___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [103, 114, 111, 98, 110, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_grobner___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_grobner___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grobner___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grobner___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grobner___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12002129749639216369 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grobner___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grobner___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grobner___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grobner___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grobner___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grobner___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grobner___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grobner: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_255_ = l_Lean_Parser_Tactic_optConfig;
    v___x_256_ = l_Lean_Parser_Tactic_grind___closed__7;
    v___x_257_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_258_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_258_, 0, v___x_257_);
    crate::leanh::lean_ctor_set(v___x_258_, 1, v___x_256_);
    crate::leanh::lean_ctor_set(v___x_258_, 2, v___x_255_);
    return v___x_258_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_269_ = l_Lean_Parser_Tactic_grind___closed__13;
    v___x_270_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__8_once),
        _init_l_Lean_Parser_Tactic_grind___closed__8,
    );
    v___x_271_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_272_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_272_, 0, v___x_271_);
    crate::leanh::lean_ctor_set(v___x_272_, 1, v___x_270_);
    crate::leanh::lean_ctor_set(v___x_272_, 2, v___x_269_);
    return v___x_272_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_283_: u8 = 0;
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = 0;
    v___x_284_ = l_Lean_Parser_Tactic_grind___closed__21;
    v___x_285_ = l_Lean_Parser_Tactic_grind___closed__19;
    v___x_286_ = l_Lean_Parser_Tactic_grindParam;
    v___x_287_ = crate::leanh::lean_alloc_ctor(10, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_287_, 0, v___x_286_);
    crate::leanh::lean_ctor_set(v___x_287_, 1, v___x_285_);
    crate::leanh::lean_ctor_set(v___x_287_, 2, v___x_284_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_287_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_283_,
    );
    return v___x_287_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_288_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__22_once),
        _init_l_Lean_Parser_Tactic_grind___closed__22,
    );
    v___x_289_ = l_Lean_Parser_Tactic_grind___closed__18;
    v___x_290_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_290_, 0, v___x_289_);
    crate::leanh::lean_ctor_set(v___x_290_, 1, v___x_288_);
    return v___x_290_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__23_once),
        _init_l_Lean_Parser_Tactic_grind___closed__23,
    );
    v___x_292_ = l_Lean_Parser_Tactic_grind___closed__16;
    v___x_293_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_294_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_294_, 0, v___x_293_);
    crate::leanh::lean_ctor_set(v___x_294_, 1, v___x_292_);
    crate::leanh::lean_ctor_set(v___x_294_, 2, v___x_291_);
    return v___x_294_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__27() -> *mut crate::leanh::LeanObject {
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = l_Lean_Parser_Tactic_grind___closed__26;
    v___x_299_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__24_once),
        _init_l_Lean_Parser_Tactic_grind___closed__24,
    );
    v___x_300_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_301_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_301_, 0, v___x_300_);
    crate::leanh::lean_ctor_set(v___x_301_, 1, v___x_299_);
    crate::leanh::lean_ctor_set(v___x_301_, 2, v___x_298_);
    return v___x_301_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_302_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__27_once),
        _init_l_Lean_Parser_Tactic_grind___closed__27,
    );
    v___x_303_ = l_Lean_Parser_Tactic_grind___closed__10;
    v___x_304_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_304_, 0, v___x_303_);
    crate::leanh::lean_ctor_set(v___x_304_, 1, v___x_302_);
    return v___x_304_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28_once),
        _init_l_Lean_Parser_Tactic_grind___closed__28,
    );
    v___x_306_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__14_once),
        _init_l_Lean_Parser_Tactic_grind___closed__14,
    );
    v___x_307_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_308_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_308_, 0, v___x_307_);
    crate::leanh::lean_ctor_set(v___x_308_, 1, v___x_306_);
    crate::leanh::lean_ctor_set(v___x_308_, 2, v___x_305_);
    return v___x_308_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__32() -> *mut crate::leanh::LeanObject {
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = l_Lean_Parser_Tactic_Grind_grindSeq;
    v___x_313_ = l_Lean_Parser_Tactic_grind___closed__31;
    v___x_314_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_315_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_315_, 0, v___x_314_);
    crate::leanh::lean_ctor_set(v___x_315_, 1, v___x_313_);
    crate::leanh::lean_ctor_set(v___x_315_, 2, v___x_312_);
    return v___x_315_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__33() -> *mut crate::leanh::LeanObject {
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_316_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__32_once),
        _init_l_Lean_Parser_Tactic_grind___closed__32,
    );
    v___x_317_ = l_Lean_Parser_Tactic_grind___closed__10;
    v___x_318_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_318_, 0, v___x_317_);
    crate::leanh::lean_ctor_set(v___x_318_, 1, v___x_316_);
    return v___x_318_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__34() -> *mut crate::leanh::LeanObject {
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_319_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__33),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__33_once),
        _init_l_Lean_Parser_Tactic_grind___closed__33,
    );
    v___x_320_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__29_once),
        _init_l_Lean_Parser_Tactic_grind___closed__29,
    );
    v___x_321_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_322_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_322_, 0, v___x_321_);
    crate::leanh::lean_ctor_set(v___x_322_, 1, v___x_320_);
    crate::leanh::lean_ctor_set(v___x_322_, 2, v___x_319_);
    return v___x_322_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__35() -> *mut crate::leanh::LeanObject {
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_323_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__34_once),
        _init_l_Lean_Parser_Tactic_grind___closed__34,
    );
    v___x_324_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_325_ = l_Lean_Parser_Tactic_grind___closed__4;
    v___x_326_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_326_, 0, v___x_325_);
    crate::leanh::lean_ctor_set(v___x_326_, 1, v___x_324_);
    crate::leanh::lean_ctor_set(v___x_326_, 2, v___x_323_);
    return v___x_326_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind() -> *mut crate::leanh::LeanObject {
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__35_once),
        _init_l_Lean_Parser_Tactic_grind___closed__35,
    );
    return v___x_327_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = l_Lean_Parser_Tactic_optConfig;
    v___x_339_ = l_Lean_Parser_Tactic_grindTrace___closed__3;
    v___x_340_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_341_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_341_, 0, v___x_340_);
    crate::leanh::lean_ctor_set(v___x_341_, 1, v___x_339_);
    crate::leanh::lean_ctor_set(v___x_341_, 2, v___x_338_);
    return v___x_341_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Parser_Tactic_grind___closed__13;
    v___x_343_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__4_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__4,
    );
    v___x_344_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_345_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_345_, 0, v___x_344_);
    crate::leanh::lean_ctor_set(v___x_345_, 1, v___x_343_);
    crate::leanh::lean_ctor_set(v___x_345_, 2, v___x_342_);
    return v___x_345_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28_once),
        _init_l_Lean_Parser_Tactic_grind___closed__28,
    );
    v___x_347_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__5_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__5,
    );
    v___x_348_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_349_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_349_, 0, v___x_348_);
    crate::leanh::lean_ctor_set(v___x_349_, 1, v___x_347_);
    crate::leanh::lean_ctor_set(v___x_349_, 2, v___x_346_);
    return v___x_349_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__6_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__6,
    );
    v___x_351_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_352_ = l_Lean_Parser_Tactic_grindTrace___closed__1;
    v___x_353_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_353_, 0, v___x_352_);
    crate::leanh::lean_ctor_set(v___x_353_, 1, v___x_351_);
    crate::leanh::lean_ctor_set(v___x_353_, 2, v___x_350_);
    return v___x_353_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace() -> *mut crate::leanh::LeanObject {
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__7_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__7,
    );
    return v___x_354_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Lean_Parser_Tactic_optConfig;
    v___x_365_ = l_Lean_Parser_Tactic_sym___closed__2;
    v___x_366_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_367_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_367_, 0, v___x_366_);
    crate::leanh::lean_ctor_set(v___x_367_, 1, v___x_365_);
    crate::leanh::lean_ctor_set(v___x_367_, 2, v___x_364_);
    return v___x_367_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Lean_Parser_Tactic_grind___closed__13;
    v___x_369_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__3_once),
        _init_l_Lean_Parser_Tactic_sym___closed__3,
    );
    v___x_370_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_371_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_371_, 0, v___x_370_);
    crate::leanh::lean_ctor_set(v___x_371_, 1, v___x_369_);
    crate::leanh::lean_ctor_set(v___x_371_, 2, v___x_368_);
    return v___x_371_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28_once),
        _init_l_Lean_Parser_Tactic_grind___closed__28,
    );
    v___x_373_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__4_once),
        _init_l_Lean_Parser_Tactic_sym___closed__4,
    );
    v___x_374_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_375_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_375_, 0, v___x_374_);
    crate::leanh::lean_ctor_set(v___x_375_, 1, v___x_373_);
    crate::leanh::lean_ctor_set(v___x_375_, 2, v___x_372_);
    return v___x_375_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = l_Lean_Parser_Tactic_grind___closed__31;
    v___x_377_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__5_once),
        _init_l_Lean_Parser_Tactic_sym___closed__5,
    );
    v___x_378_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_379_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_379_, 0, v___x_378_);
    crate::leanh::lean_ctor_set(v___x_379_, 1, v___x_377_);
    crate::leanh::lean_ctor_set(v___x_379_, 2, v___x_376_);
    return v___x_379_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Parser_Tactic_Grind_grindSeq;
    v___x_381_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__6_once),
        _init_l_Lean_Parser_Tactic_sym___closed__6,
    );
    v___x_382_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_383_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_383_, 0, v___x_382_);
    crate::leanh::lean_ctor_set(v___x_383_, 1, v___x_381_);
    crate::leanh::lean_ctor_set(v___x_383_, 2, v___x_380_);
    return v___x_383_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__7_once),
        _init_l_Lean_Parser_Tactic_sym___closed__7,
    );
    v___x_385_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_386_ = l_Lean_Parser_Tactic_sym___closed__1;
    v___x_387_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_387_, 0, v___x_386_);
    crate::leanh::lean_ctor_set(v___x_387_, 1, v___x_385_);
    crate::leanh::lean_ctor_set(v___x_387_, 2, v___x_384_);
    return v___x_387_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym() -> *mut crate::leanh::LeanObject {
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__8_once),
        _init_l_Lean_Parser_Tactic_sym___closed__8,
    );
    return v___x_388_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_cutsat___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = l_Lean_Parser_Tactic_optConfig;
    v___x_399_ = l_Lean_Parser_Tactic_cutsat___closed__2;
    v___x_400_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_401_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_401_, 0, v___x_400_);
    crate::leanh::lean_ctor_set(v___x_401_, 1, v___x_399_);
    crate::leanh::lean_ctor_set(v___x_401_, 2, v___x_398_);
    return v___x_401_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_cutsat___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__3_once),
        _init_l_Lean_Parser_Tactic_cutsat___closed__3,
    );
    v___x_403_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_404_ = l_Lean_Parser_Tactic_cutsat___closed__1;
    v___x_405_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_405_, 0, v___x_404_);
    crate::leanh::lean_ctor_set(v___x_405_, 1, v___x_403_);
    crate::leanh::lean_ctor_set(v___x_405_, 2, v___x_402_);
    return v___x_405_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_cutsat() -> *mut crate::leanh::LeanObject {
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__4_once),
        _init_l_Lean_Parser_Tactic_cutsat___closed__4,
    );
    return v___x_406_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_lia___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = l_Lean_Parser_Tactic_optConfig;
    v___x_417_ = l_Lean_Parser_Tactic_lia___closed__2;
    v___x_418_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_419_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_419_, 0, v___x_418_);
    crate::leanh::lean_ctor_set(v___x_419_, 1, v___x_417_);
    crate::leanh::lean_ctor_set(v___x_419_, 2, v___x_416_);
    return v___x_419_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_lia___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__3_once),
        _init_l_Lean_Parser_Tactic_lia___closed__3,
    );
    v___x_421_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_422_ = l_Lean_Parser_Tactic_lia___closed__1;
    v___x_423_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_423_, 0, v___x_422_);
    crate::leanh::lean_ctor_set(v___x_423_, 1, v___x_421_);
    crate::leanh::lean_ctor_set(v___x_423_, 2, v___x_420_);
    return v___x_423_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_lia() -> *mut crate::leanh::LeanObject {
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__4_once),
        _init_l_Lean_Parser_Tactic_lia___closed__4,
    );
    return v___x_424_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__order___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = l_Lean_Parser_Tactic_optConfig;
    v___x_435_ = l_Lean_Parser_Tactic_grind__order___closed__2;
    v___x_436_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_437_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_437_, 0, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_437_, 1, v___x_435_);
    crate::leanh::lean_ctor_set(v___x_437_, 2, v___x_434_);
    return v___x_437_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__order___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__3_once),
        _init_l_Lean_Parser_Tactic_grind__order___closed__3,
    );
    v___x_439_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_440_ = l_Lean_Parser_Tactic_grind__order___closed__1;
    v___x_441_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_441_, 0, v___x_440_);
    crate::leanh::lean_ctor_set(v___x_441_, 1, v___x_439_);
    crate::leanh::lean_ctor_set(v___x_441_, 2, v___x_438_);
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__order() -> *mut crate::leanh::LeanObject {
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_442_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__4_once),
        _init_l_Lean_Parser_Tactic_grind__order___closed__4,
    );
    return v___x_442_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__linarith___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = l_Lean_Parser_Tactic_optConfig;
    v___x_453_ = l_Lean_Parser_Tactic_grind__linarith___closed__2;
    v___x_454_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_455_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_455_, 0, v___x_454_);
    crate::leanh::lean_ctor_set(v___x_455_, 1, v___x_453_);
    crate::leanh::lean_ctor_set(v___x_455_, 2, v___x_452_);
    return v___x_455_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__linarith___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__3_once),
        _init_l_Lean_Parser_Tactic_grind__linarith___closed__3,
    );
    v___x_457_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_458_ = l_Lean_Parser_Tactic_grind__linarith___closed__1;
    v___x_459_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_458_);
    crate::leanh::lean_ctor_set(v___x_459_, 1, v___x_457_);
    crate::leanh::lean_ctor_set(v___x_459_, 2, v___x_456_);
    return v___x_459_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__linarith() -> *mut crate::leanh::LeanObject {
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_460_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__4_once),
        _init_l_Lean_Parser_Tactic_grind__linarith___closed__4,
    );
    return v___x_460_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grobner___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_470_ = l_Lean_Parser_Tactic_optConfig;
    v___x_471_ = l_Lean_Parser_Tactic_grobner___closed__2;
    v___x_472_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_473_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_473_, 0, v___x_472_);
    crate::leanh::lean_ctor_set(v___x_473_, 1, v___x_471_);
    crate::leanh::lean_ctor_set(v___x_473_, 2, v___x_470_);
    return v___x_473_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grobner___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__3_once),
        _init_l_Lean_Parser_Tactic_grobner___closed__3,
    );
    v___x_475_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_476_ = l_Lean_Parser_Tactic_grobner___closed__1;
    v___x_477_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_477_, 0, v___x_476_);
    crate::leanh::lean_ctor_set(v___x_477_, 1, v___x_475_);
    crate::leanh::lean_ctor_set(v___x_477_, 2, v___x_474_);
    return v___x_477_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grobner() -> *mut crate::leanh::LeanObject {
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__4_once),
        _init_l_Lean_Parser_Tactic_grobner___closed__4,
    );
    return v___x_478_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Tactics(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Interactive(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Tactics(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Tactic_grind = _init_l_Lean_Parser_Tactic_grind();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grind);
    l_Lean_Parser_Tactic_grindTrace = _init_l_Lean_Parser_Tactic_grindTrace();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace);
    l_Lean_Parser_Tactic_sym = _init_l_Lean_Parser_Tactic_sym();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_sym);
    l_Lean_Parser_Tactic_cutsat = _init_l_Lean_Parser_Tactic_cutsat();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_cutsat);
    l_Lean_Parser_Tactic_lia = _init_l_Lean_Parser_Tactic_lia();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_lia);
    l_Lean_Parser_Tactic_grind__order = _init_l_Lean_Parser_Tactic_grind__order();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grind__order);
    l_Lean_Parser_Tactic_grind__linarith = _init_l_Lean_Parser_Tactic_grind__linarith();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grind__linarith);
    l_Lean_Parser_Tactic_grobner = _init_l_Lean_Parser_Tactic_grobner();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grobner);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Tactics(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Interactive(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Tactics(builtin);
}
