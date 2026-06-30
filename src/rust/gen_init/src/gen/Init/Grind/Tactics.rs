// Lean compiler output
// Module: Init.Grind.Tactics
// Imports: Init.Core Init.Grind.Interactive
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Grind::Interactive::{
    initialize_Init_Grind_Interactive, l_Lean_Parser_Tactic_Grind_grindSeq,
    l_Lean_Parser_Tactic_grindParam, runtime_initialize_Init_Grind_Interactive,
};
use crate::r#gen::Init::Tactics::l_Lean_Parser_Tactic_optConfig;
pub static l_Lean_Parser_Tactic_grind___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_grind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Tactic_grind___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__2_value: leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Tactic_grind___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__3_value: leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_grind___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grind___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__3_value)
                as *mut leanh::LeanObject,
            7213727686127018646 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__5_value: leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__5_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__3_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__9_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_grind___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__9_value)
                as *mut leanh::LeanObject,
            18170484695678750185 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__11_value: leanh::LeanStringObject<6> =
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
        m_data: [32, 111, 110, 108, 121, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__11_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__15_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_grind___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__16_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__17_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_grind___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__17_value)
                as *mut leanh::LeanObject,
            1164644006045091397 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__19_value: leanh::LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__20_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_grind___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__21_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__25_value: leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__26_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__25_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__26_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__30_value: leanh::LeanStringObject<5> =
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
        m_data: [32, 61, 62, 32, 0],
    };
static mut l_Lean_Parser_Tactic_grind___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__31_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__30_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__31_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__33_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__33: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__35_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grind: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grindTrace___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_grindTrace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grindTrace___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__0_value)
                as *mut leanh::LeanObject,
            8341917469546378704 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grindTrace___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [103, 114, 105, 110, 100, 63, 0],
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grindTrace___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grindTrace___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindTrace___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindTrace___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindTrace___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grindTrace: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_sym___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_sym___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_sym___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_sym___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_sym___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_sym___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__0_value)
                as *mut leanh::LeanObject,
            2698983533533738959 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_sym___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_sym___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__0_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_sym___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_sym___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_sym___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_sym: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_cutsat___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [99, 117, 116, 115, 97, 116, 0],
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_cutsat___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__0_value)
                as *mut leanh::LeanObject,
            2518545331120607024 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_cutsat___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__0_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_cutsat___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_cutsat___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_cutsat___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_cutsat: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_lia___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_lia___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_lia___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_lia___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_lia___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_lia___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__0_value)
                as *mut leanh::LeanObject,
            628853965465602645 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_lia___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_lia___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__0_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_lia___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_lia___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_lia___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_lia___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_lia___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_lia: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind__order___closed__0_value: leanh::LeanStringObject<12> =
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
        m_data: [103, 114, 105, 110, 100, 95, 111, 114, 100, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grind__order___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__0_value)
                as *mut leanh::LeanObject,
            6376312911296474159 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind__order___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__0_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind__order___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind__order___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grind__order: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind__linarith___closed__0_value: leanh::LeanStringObject<
    15,
> = leanh::LeanStringObject {
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
        103, 114, 105, 110, 100, 95, 108, 105, 110, 97, 114, 105, 116, 104, 0,
    ],
};
static mut l_Lean_Parser_Tactic_grind__linarith___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_grind__linarith___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__0_value)
                as *mut leanh::LeanObject,
            6166429773221086783 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grind__linarith___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__0_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grind__linarith___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind__linarith___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grind__linarith: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grobner___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [103, 114, 111, 98, 110, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_grobner___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_grobner___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grobner___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grobner___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grobner___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__0_value)
                as *mut leanh::LeanObject,
            12002129749639216369 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grobner___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_grobner___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__0_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grobner___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_grobner___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grobner___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grobner___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_grobner___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grobner: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_255_ = l_Lean_Parser_Tactic_optConfig;
    v___x_256_ = l_Lean_Parser_Tactic_grind___closed__7;
    v___x_257_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_258_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_258_, 0, v___x_257_);
    leanh::lean_ctor_set(v___x_258_, 1, v___x_256_);
    leanh::lean_ctor_set(v___x_258_, 2, v___x_255_);
    return v___x_258_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_269_ = l_Lean_Parser_Tactic_grind___closed__13;
    v___x_270_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__8_once),
        _init_l_Lean_Parser_Tactic_grind___closed__8,
    );
    v___x_271_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_272_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_272_, 0, v___x_271_);
    leanh::lean_ctor_set(v___x_272_, 1, v___x_270_);
    leanh::lean_ctor_set(v___x_272_, 2, v___x_269_);
    return v___x_272_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_283_: u8 = 0;
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = 0;
    v___x_284_ = l_Lean_Parser_Tactic_grind___closed__21;
    v___x_285_ = l_Lean_Parser_Tactic_grind___closed__19;
    v___x_286_ = l_Lean_Parser_Tactic_grindParam;
    v___x_287_ = leanh::lean_alloc_ctor(10, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_287_, 0, v___x_286_);
    leanh::lean_ctor_set(v___x_287_, 1, v___x_285_);
    leanh::lean_ctor_set(v___x_287_, 2, v___x_284_);
    leanh::lean_ctor_set_uint8(
        v___x_287_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_283_,
    );
    return v___x_287_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_288_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__22_once),
        _init_l_Lean_Parser_Tactic_grind___closed__22,
    );
    v___x_289_ = l_Lean_Parser_Tactic_grind___closed__18;
    v___x_290_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_290_, 0, v___x_289_);
    leanh::lean_ctor_set(v___x_290_, 1, v___x_288_);
    return v___x_290_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__23_once),
        _init_l_Lean_Parser_Tactic_grind___closed__23,
    );
    v___x_292_ = l_Lean_Parser_Tactic_grind___closed__16;
    v___x_293_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_294_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_294_, 0, v___x_293_);
    leanh::lean_ctor_set(v___x_294_, 1, v___x_292_);
    leanh::lean_ctor_set(v___x_294_, 2, v___x_291_);
    return v___x_294_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = l_Lean_Parser_Tactic_grind___closed__26;
    v___x_299_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__24_once),
        _init_l_Lean_Parser_Tactic_grind___closed__24,
    );
    v___x_300_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_301_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_301_, 0, v___x_300_);
    leanh::lean_ctor_set(v___x_301_, 1, v___x_299_);
    leanh::lean_ctor_set(v___x_301_, 2, v___x_298_);
    return v___x_301_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__28() -> *mut leanh::LeanObject {
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_302_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__27_once),
        _init_l_Lean_Parser_Tactic_grind___closed__27,
    );
    v___x_303_ = l_Lean_Parser_Tactic_grind___closed__10;
    v___x_304_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_304_, 0, v___x_303_);
    leanh::lean_ctor_set(v___x_304_, 1, v___x_302_);
    return v___x_304_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__29() -> *mut leanh::LeanObject {
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28_once),
        _init_l_Lean_Parser_Tactic_grind___closed__28,
    );
    v___x_306_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__14_once),
        _init_l_Lean_Parser_Tactic_grind___closed__14,
    );
    v___x_307_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_308_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_308_, 0, v___x_307_);
    leanh::lean_ctor_set(v___x_308_, 1, v___x_306_);
    leanh::lean_ctor_set(v___x_308_, 2, v___x_305_);
    return v___x_308_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__32() -> *mut leanh::LeanObject {
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = l_Lean_Parser_Tactic_Grind_grindSeq;
    v___x_313_ = l_Lean_Parser_Tactic_grind___closed__31;
    v___x_314_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_315_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_315_, 0, v___x_314_);
    leanh::lean_ctor_set(v___x_315_, 1, v___x_313_);
    leanh::lean_ctor_set(v___x_315_, 2, v___x_312_);
    return v___x_315_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__33() -> *mut leanh::LeanObject {
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_316_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__32_once),
        _init_l_Lean_Parser_Tactic_grind___closed__32,
    );
    v___x_317_ = l_Lean_Parser_Tactic_grind___closed__10;
    v___x_318_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_318_, 0, v___x_317_);
    leanh::lean_ctor_set(v___x_318_, 1, v___x_316_);
    return v___x_318_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__34() -> *mut leanh::LeanObject {
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_319_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__33),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__33_once),
        _init_l_Lean_Parser_Tactic_grind___closed__33,
    );
    v___x_320_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__29_once),
        _init_l_Lean_Parser_Tactic_grind___closed__29,
    );
    v___x_321_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_322_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_322_, 0, v___x_321_);
    leanh::lean_ctor_set(v___x_322_, 1, v___x_320_);
    leanh::lean_ctor_set(v___x_322_, 2, v___x_319_);
    return v___x_322_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__35() -> *mut leanh::LeanObject {
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_323_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__34_once),
        _init_l_Lean_Parser_Tactic_grind___closed__34,
    );
    v___x_324_ = leanh::lean_unsigned_to_nat(1022);
    v___x_325_ = l_Lean_Parser_Tactic_grind___closed__4;
    v___x_326_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_326_, 0, v___x_325_);
    leanh::lean_ctor_set(v___x_326_, 1, v___x_324_);
    leanh::lean_ctor_set(v___x_326_, 2, v___x_323_);
    return v___x_326_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind() -> *mut leanh::LeanObject {
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__35_once),
        _init_l_Lean_Parser_Tactic_grind___closed__35,
    );
    return v___x_327_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = l_Lean_Parser_Tactic_optConfig;
    v___x_339_ = l_Lean_Parser_Tactic_grindTrace___closed__3;
    v___x_340_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_341_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_341_, 0, v___x_340_);
    leanh::lean_ctor_set(v___x_341_, 1, v___x_339_);
    leanh::lean_ctor_set(v___x_341_, 2, v___x_338_);
    return v___x_341_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Parser_Tactic_grind___closed__13;
    v___x_343_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__4_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__4,
    );
    v___x_344_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_345_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_345_, 0, v___x_344_);
    leanh::lean_ctor_set(v___x_345_, 1, v___x_343_);
    leanh::lean_ctor_set(v___x_345_, 2, v___x_342_);
    return v___x_345_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28_once),
        _init_l_Lean_Parser_Tactic_grind___closed__28,
    );
    v___x_347_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__5_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__5,
    );
    v___x_348_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_349_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_349_, 0, v___x_348_);
    leanh::lean_ctor_set(v___x_349_, 1, v___x_347_);
    leanh::lean_ctor_set(v___x_349_, 2, v___x_346_);
    return v___x_349_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__6_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__6,
    );
    v___x_351_ = leanh::lean_unsigned_to_nat(1022);
    v___x_352_ = l_Lean_Parser_Tactic_grindTrace___closed__1;
    v___x_353_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_353_, 0, v___x_352_);
    leanh::lean_ctor_set(v___x_353_, 1, v___x_351_);
    leanh::lean_ctor_set(v___x_353_, 2, v___x_350_);
    return v___x_353_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace() -> *mut leanh::LeanObject {
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__7_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__7,
    );
    return v___x_354_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Lean_Parser_Tactic_optConfig;
    v___x_365_ = l_Lean_Parser_Tactic_sym___closed__2;
    v___x_366_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_367_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_367_, 0, v___x_366_);
    leanh::lean_ctor_set(v___x_367_, 1, v___x_365_);
    leanh::lean_ctor_set(v___x_367_, 2, v___x_364_);
    return v___x_367_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Lean_Parser_Tactic_grind___closed__13;
    v___x_369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__3_once),
        _init_l_Lean_Parser_Tactic_sym___closed__3,
    );
    v___x_370_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_371_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_371_, 0, v___x_370_);
    leanh::lean_ctor_set(v___x_371_, 1, v___x_369_);
    leanh::lean_ctor_set(v___x_371_, 2, v___x_368_);
    return v___x_371_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28_once),
        _init_l_Lean_Parser_Tactic_grind___closed__28,
    );
    v___x_373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__4_once),
        _init_l_Lean_Parser_Tactic_sym___closed__4,
    );
    v___x_374_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_375_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_375_, 0, v___x_374_);
    leanh::lean_ctor_set(v___x_375_, 1, v___x_373_);
    leanh::lean_ctor_set(v___x_375_, 2, v___x_372_);
    return v___x_375_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = l_Lean_Parser_Tactic_grind___closed__31;
    v___x_377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__5_once),
        _init_l_Lean_Parser_Tactic_sym___closed__5,
    );
    v___x_378_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_379_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_379_, 0, v___x_378_);
    leanh::lean_ctor_set(v___x_379_, 1, v___x_377_);
    leanh::lean_ctor_set(v___x_379_, 2, v___x_376_);
    return v___x_379_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Parser_Tactic_Grind_grindSeq;
    v___x_381_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__6_once),
        _init_l_Lean_Parser_Tactic_sym___closed__6,
    );
    v___x_382_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_383_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_383_, 0, v___x_382_);
    leanh::lean_ctor_set(v___x_383_, 1, v___x_381_);
    leanh::lean_ctor_set(v___x_383_, 2, v___x_380_);
    return v___x_383_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__7_once),
        _init_l_Lean_Parser_Tactic_sym___closed__7,
    );
    v___x_385_ = leanh::lean_unsigned_to_nat(1022);
    v___x_386_ = l_Lean_Parser_Tactic_sym___closed__1;
    v___x_387_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_387_, 0, v___x_386_);
    leanh::lean_ctor_set(v___x_387_, 1, v___x_385_);
    leanh::lean_ctor_set(v___x_387_, 2, v___x_384_);
    return v___x_387_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym() -> *mut leanh::LeanObject {
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__8_once),
        _init_l_Lean_Parser_Tactic_sym___closed__8,
    );
    return v___x_388_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_cutsat___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = l_Lean_Parser_Tactic_optConfig;
    v___x_399_ = l_Lean_Parser_Tactic_cutsat___closed__2;
    v___x_400_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_401_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_401_, 0, v___x_400_);
    leanh::lean_ctor_set(v___x_401_, 1, v___x_399_);
    leanh::lean_ctor_set(v___x_401_, 2, v___x_398_);
    return v___x_401_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_cutsat___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__3_once),
        _init_l_Lean_Parser_Tactic_cutsat___closed__3,
    );
    v___x_403_ = leanh::lean_unsigned_to_nat(1022);
    v___x_404_ = l_Lean_Parser_Tactic_cutsat___closed__1;
    v___x_405_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_405_, 0, v___x_404_);
    leanh::lean_ctor_set(v___x_405_, 1, v___x_403_);
    leanh::lean_ctor_set(v___x_405_, 2, v___x_402_);
    return v___x_405_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_cutsat() -> *mut leanh::LeanObject {
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__4_once),
        _init_l_Lean_Parser_Tactic_cutsat___closed__4,
    );
    return v___x_406_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_lia___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = l_Lean_Parser_Tactic_optConfig;
    v___x_417_ = l_Lean_Parser_Tactic_lia___closed__2;
    v___x_418_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_419_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_419_, 0, v___x_418_);
    leanh::lean_ctor_set(v___x_419_, 1, v___x_417_);
    leanh::lean_ctor_set(v___x_419_, 2, v___x_416_);
    return v___x_419_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_lia___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__3_once),
        _init_l_Lean_Parser_Tactic_lia___closed__3,
    );
    v___x_421_ = leanh::lean_unsigned_to_nat(1022);
    v___x_422_ = l_Lean_Parser_Tactic_lia___closed__1;
    v___x_423_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_423_, 0, v___x_422_);
    leanh::lean_ctor_set(v___x_423_, 1, v___x_421_);
    leanh::lean_ctor_set(v___x_423_, 2, v___x_420_);
    return v___x_423_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_lia() -> *mut leanh::LeanObject {
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__4_once),
        _init_l_Lean_Parser_Tactic_lia___closed__4,
    );
    return v___x_424_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__order___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = l_Lean_Parser_Tactic_optConfig;
    v___x_435_ = l_Lean_Parser_Tactic_grind__order___closed__2;
    v___x_436_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_437_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_437_, 0, v___x_436_);
    leanh::lean_ctor_set(v___x_437_, 1, v___x_435_);
    leanh::lean_ctor_set(v___x_437_, 2, v___x_434_);
    return v___x_437_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__order___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__3_once),
        _init_l_Lean_Parser_Tactic_grind__order___closed__3,
    );
    v___x_439_ = leanh::lean_unsigned_to_nat(1022);
    v___x_440_ = l_Lean_Parser_Tactic_grind__order___closed__1;
    v___x_441_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_441_, 0, v___x_440_);
    leanh::lean_ctor_set(v___x_441_, 1, v___x_439_);
    leanh::lean_ctor_set(v___x_441_, 2, v___x_438_);
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__order() -> *mut leanh::LeanObject {
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_442_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__4_once),
        _init_l_Lean_Parser_Tactic_grind__order___closed__4,
    );
    return v___x_442_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__linarith___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = l_Lean_Parser_Tactic_optConfig;
    v___x_453_ = l_Lean_Parser_Tactic_grind__linarith___closed__2;
    v___x_454_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_455_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_455_, 0, v___x_454_);
    leanh::lean_ctor_set(v___x_455_, 1, v___x_453_);
    leanh::lean_ctor_set(v___x_455_, 2, v___x_452_);
    return v___x_455_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__linarith___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__3_once),
        _init_l_Lean_Parser_Tactic_grind__linarith___closed__3,
    );
    v___x_457_ = leanh::lean_unsigned_to_nat(1022);
    v___x_458_ = l_Lean_Parser_Tactic_grind__linarith___closed__1;
    v___x_459_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_459_, 0, v___x_458_);
    leanh::lean_ctor_set(v___x_459_, 1, v___x_457_);
    leanh::lean_ctor_set(v___x_459_, 2, v___x_456_);
    return v___x_459_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__linarith() -> *mut leanh::LeanObject {
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_460_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__4_once),
        _init_l_Lean_Parser_Tactic_grind__linarith___closed__4,
    );
    return v___x_460_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grobner___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_470_ = l_Lean_Parser_Tactic_optConfig;
    v___x_471_ = l_Lean_Parser_Tactic_grobner___closed__2;
    v___x_472_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_473_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_473_, 0, v___x_472_);
    leanh::lean_ctor_set(v___x_473_, 1, v___x_471_);
    leanh::lean_ctor_set(v___x_473_, 2, v___x_470_);
    return v___x_473_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grobner___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__3_once),
        _init_l_Lean_Parser_Tactic_grobner___closed__3,
    );
    v___x_475_ = leanh::lean_unsigned_to_nat(1022);
    v___x_476_ = l_Lean_Parser_Tactic_grobner___closed__1;
    v___x_477_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_477_, 0, v___x_476_);
    leanh::lean_ctor_set(v___x_477_, 1, v___x_475_);
    leanh::lean_ctor_set(v___x_477_, 2, v___x_474_);
    return v___x_477_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grobner() -> *mut leanh::LeanObject {
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__4_once),
        _init_l_Lean_Parser_Tactic_grobner___closed__4,
    );
    return v___x_478_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Tactics(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Interactive(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Tactics(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Tactic_grind = _init_l_Lean_Parser_Tactic_grind();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grind);
    l_Lean_Parser_Tactic_grindTrace = _init_l_Lean_Parser_Tactic_grindTrace();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace);
    l_Lean_Parser_Tactic_sym = _init_l_Lean_Parser_Tactic_sym();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_sym);
    l_Lean_Parser_Tactic_cutsat = _init_l_Lean_Parser_Tactic_cutsat();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_cutsat);
    l_Lean_Parser_Tactic_lia = _init_l_Lean_Parser_Tactic_lia();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_lia);
    l_Lean_Parser_Tactic_grind__order = _init_l_Lean_Parser_Tactic_grind__order();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grind__order);
    l_Lean_Parser_Tactic_grind__linarith = _init_l_Lean_Parser_Tactic_grind__linarith();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grind__linarith);
    l_Lean_Parser_Tactic_grobner = _init_l_Lean_Parser_Tactic_grobner();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_grobner);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Tactics(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Interactive(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Tactics(builtin);
}