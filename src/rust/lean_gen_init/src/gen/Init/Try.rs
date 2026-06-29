// Lean compiler output
// Module: Init.Try
// Imports: Init.Tactics
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node5, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_optConfig, runtime_initialize_Init_Tactics,
};
pub static l_Lean_Try_instInhabitedConfig_default___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((8 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        281479271678209 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Try_instInhabitedConfig_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Try_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Try_instInhabitedConfig_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Try_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Try_instInhabitedConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Try_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTrace___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_tryTrace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTrace___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Tactic_tryTrace___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTrace___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Tactic_tryTrace___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTrace___closed__3_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [116, 114, 121, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_tryTrace___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_tryTrace___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__3_value)
                as *mut crate::leanh::LeanObject,
            1540710835455164638 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryTrace___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTrace___closed__5_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lean_Parser_Tactic_tryTrace___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTrace___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__5_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryTrace___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTrace___closed__7_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 121, 63, 0],
    };
static mut l_Lean_Parser_Tactic_tryTrace___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTrace___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__7_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryTrace___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_tryTrace___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tryTrace___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_tryTrace___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tryTrace___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_tryTrace: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_tryTraceWith___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [116, 114, 121, 84, 114, 97, 99, 101, 87, 105, 116, 104, 0],
    };
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_tryTraceWith___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7620727169695373581 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTraceWith___closed__2_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTraceWith___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_tryTraceWith___closed__5_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTraceWith___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__5_value)
                as *mut crate::leanh::LeanObject,
            11103865283154438669 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryTraceWith___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tryTraceWith___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_tryTraceWith: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_attemptAll___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [97, 116, 116, 101, 109, 112, 116, 65, 108, 108, 0],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_attemptAll___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15398789673399806458 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__2_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [97, 116, 116, 101, 109, 112, 116, 95, 97, 108, 108, 32, 0],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__4_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [119, 105, 116, 104, 80, 111, 115, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__4_value)
                as *mut crate::leanh::LeanObject,
            17180264478054591478 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__6_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [109, 97, 110, 121, 49, 0],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17243740965612849207 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__8_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__8_value)
                as *mut crate::leanh::LeanObject,
            2214559063752339918 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__10_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [112, 112, 68, 101, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__10_value)
                as *mut crate::leanh::LeanObject,
            2710995909225096690 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__12_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [112, 112, 76, 105, 110, 101, 0],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__12_value)
                as *mut crate::leanh::LeanObject,
            4227538229121138037 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__14_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__15_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__16_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 111, 108, 71, 101, 0],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__16_value)
                as *mut crate::leanh::LeanObject,
            4942254933594350711 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__18_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__19_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__20_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [124, 32, 0],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__21_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__22_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__19_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__23_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__22_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__24_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__25_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__26_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__25_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__27_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAll___closed__28_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__27_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAll___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_attemptAll: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAllPar___closed__0_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        97, 116, 116, 101, 109, 112, 116, 65, 108, 108, 80, 97, 114, 0,
    ],
};
static mut l_Lean_Parser_Tactic_attemptAllPar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_attemptAllPar___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18409582741206092126 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAllPar___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAllPar___closed__2_value: crate::leanh::LeanStringObject<
    17,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        97, 116, 116, 101, 109, 112, 116, 95, 97, 108, 108, 95, 112, 97, 114, 32, 0,
    ],
};
static mut l_Lean_Parser_Tactic_attemptAllPar___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAllPar___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAllPar___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAllPar___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAllPar___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_attemptAllPar___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_attemptAllPar___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_attemptAllPar: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAllPar___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_firstPar___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [102, 105, 114, 115, 116, 80, 97, 114, 0],
    };
static mut l_Lean_Parser_Tactic_firstPar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_firstPar___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__0_value)
                as *mut crate::leanh::LeanObject,
            568984433564265394 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_firstPar___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_firstPar___closed__2_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [102, 105, 114, 115, 116, 95, 112, 97, 114, 32, 0],
    };
static mut l_Lean_Parser_Tactic_firstPar___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_firstPar___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_firstPar___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_firstPar___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_attemptAll___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_firstPar___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_firstPar___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_firstPar___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_firstPar: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_firstPar___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [116, 114, 121, 82, 101, 115, 117, 108, 116, 0],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_tryResult___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12577657093477145008 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__2_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            116, 114, 121, 95, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [109, 97, 110, 121, 0],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__4_value)
                as *mut crate::leanh::LeanObject,
            2302572775315350313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__6_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [116, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__6_value)
                as *mut crate::leanh::LeanObject,
            16145843736367156323 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__7_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tryResult___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_tryResult___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_tryResult: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tryResult___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__1_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 84, 114, 121, 84, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_registerTryTactic___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__1_value)
            as *mut crate::leanh::LeanObject,
        2224308280660100416 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__3_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Parser_Command_registerTryTactic___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__4_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18170484695678750185 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__5_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__6_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__5_value)
            as *mut crate::leanh::LeanObject,
        3961966953292576997 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__7_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__8_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__9_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 95, 116, 114, 121, 63, 95, 116, 97, 99, 116, 105,
        99, 0,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__10_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__12_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Parser_Command_registerTryTactic___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__13_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__14_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [112, 114, 105, 111, 114, 105, 116, 121, 0],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__15_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__14_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__17_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 61, 0],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__18_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__17_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__19_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__20_value:
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
    m_data: [110, 117, 109, 0],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__21_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__20_value)
            as *mut crate::leanh::LeanObject,
        6110315075117401315 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__22_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__21_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__23_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__22_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__24_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Parser_Command_registerTryTactic___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__25_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__24_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__26_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__23_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__25_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__27_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__26_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__28_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__27_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__29_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__28_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerTryTactic___closed__30_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__2_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__29_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerTryTactic___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Command_registerTryTactic: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerTryTactic___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_tactic_u220e___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 226, 136, 142, 0],
    };
static mut l_tactic_u220e___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_tactic_u220e___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_tactic_u220e___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_tactic_u220e___closed__0_value) as *mut crate::leanh::LeanObject,
            17790349622111278261 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_tactic_u220e___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_tactic_u220e___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_tactic_u220e___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [226, 136, 142, 0],
    };
static mut l_tactic_u220e___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_tactic_u220e___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_tactic_u220e___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_tactic_u220e___closed__2_value) as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_tactic_u220e___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_tactic_u220e___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_tactic_u220e___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_tactic_u220e___closed__1_value) as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_tactic_u220e___closed__3_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_tactic_u220e___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_tactic_u220e___closed__4_value) as *mut crate::leanh::LeanObject;
pub static mut l_tactic_u220e: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_tactic_u220e___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__tactic_u220e__1___closed__0_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l___aux__Init__Try______macroRules__tactic_u220e__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__tactic_u220e__1___closed__2_value:
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
static mut l___aux__Init__Try______macroRules__tactic_u220e__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3_value:
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
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_term_u220e___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 5,
        m_data: [116, 101, 114, 109, 226, 136, 142, 0],
    };
static mut l_term_u220e___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_u220e___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_term_u220e___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_u220e___closed__0_value) as *mut crate::leanh::LeanObject,
            8478466739506436372 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_u220e___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_u220e___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_term_u220e___closed__2_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_tactic_u220e___closed__2_value) as *mut crate::leanh::LeanObject
        ],
    };
static mut l_term_u220e___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_u220e___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_term_u220e___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_u220e___closed__1_value) as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_u220e___closed__2_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_u220e___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_u220e___closed__3_value) as *mut crate::leanh::LeanObject;
pub static mut l_term_u220e: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_u220e___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__0_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__1_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16173796135615239867 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__3_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [98, 121, 0],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTraceWith___closed__5_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__5_value:
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
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__7_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__7_value)
            as *mut crate::leanh::LeanObject,
        10138443044734372301 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__9_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tryTrace___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__9_value)
            as *mut crate::leanh::LeanObject,
        13577612981047608199 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__11_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [119, 114, 97, 112, 87, 105, 116, 104, 66, 121, 0],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__13_value:
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
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__11_value)
            as *mut crate::leanh::LeanObject,
        1067582380865326774 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__14_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__16_value:
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
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        6560861498103128555 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__17_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value_aux_0:
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
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__17_value)
            as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        9255189395584251158 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__19_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Try______macroRules__term_u220e__1___closed__20_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__19_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Try______macroRules__term_u220e__1___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___aux__Init__Try______macroRules__term_u220e__1___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Parser_Tactic_tryTrace___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_496_ = l_Lean_Parser_Tactic_optConfig;
    v___x_497_ = l_Lean_Parser_Tactic_tryTrace___closed__8;
    v___x_498_ = l_Lean_Parser_Tactic_tryTrace___closed__6;
    v___x_499_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_499_, 0, v___x_498_);
    crate::leanh::lean_ctor_set(v___x_499_, 1, v___x_497_);
    crate::leanh::lean_ctor_set(v___x_499_, 2, v___x_496_);
    return v___x_499_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tryTrace___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_500_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTrace___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTrace___closed__9_once),
        _init_l_Lean_Parser_Tactic_tryTrace___closed__9,
    );
    v___x_501_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_502_ = l_Lean_Parser_Tactic_tryTrace___closed__4;
    v___x_503_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_503_, 0, v___x_502_);
    crate::leanh::lean_ctor_set(v___x_503_, 1, v___x_501_);
    crate::leanh::lean_ctor_set(v___x_503_, 2, v___x_500_);
    return v___x_503_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tryTrace() -> *mut crate::leanh::LeanObject {
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_504_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTrace___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTrace___closed__10_once),
        _init_l_Lean_Parser_Tactic_tryTrace___closed__10,
    );
    return v___x_504_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tryTraceWith___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = l_Lean_Parser_Tactic_tryTraceWith___closed__3;
    v___x_515_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTrace___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTrace___closed__9_once),
        _init_l_Lean_Parser_Tactic_tryTrace___closed__9,
    );
    v___x_516_ = l_Lean_Parser_Tactic_tryTrace___closed__6;
    v___x_517_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_517_, 0, v___x_516_);
    crate::leanh::lean_ctor_set(v___x_517_, 1, v___x_515_);
    crate::leanh::lean_ctor_set(v___x_517_, 2, v___x_514_);
    return v___x_517_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tryTraceWith___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_523_ = l_Lean_Parser_Tactic_tryTraceWith___closed__7;
    v___x_524_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTraceWith___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTraceWith___closed__4_once),
        _init_l_Lean_Parser_Tactic_tryTraceWith___closed__4,
    );
    v___x_525_ = l_Lean_Parser_Tactic_tryTrace___closed__6;
    v___x_526_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_526_, 0, v___x_525_);
    crate::leanh::lean_ctor_set(v___x_526_, 1, v___x_524_);
    crate::leanh::lean_ctor_set(v___x_526_, 2, v___x_523_);
    return v___x_526_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tryTraceWith___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_527_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTraceWith___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTraceWith___closed__8_once),
        _init_l_Lean_Parser_Tactic_tryTraceWith___closed__8,
    );
    v___x_528_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_529_ = l_Lean_Parser_Tactic_tryTraceWith___closed__1;
    v___x_530_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_530_, 0, v___x_529_);
    crate::leanh::lean_ctor_set(v___x_530_, 1, v___x_528_);
    crate::leanh::lean_ctor_set(v___x_530_, 2, v___x_527_);
    return v___x_530_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tryTraceWith() -> *mut crate::leanh::LeanObject {
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_531_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTraceWith___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tryTraceWith___closed__9_once),
        _init_l_Lean_Parser_Tactic_tryTraceWith___closed__9,
    );
    return v___x_531_;
}
pub unsafe fn _init_l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_765_;
}
pub unsafe fn l___aux__Init__Try______macroRules__tactic_u220e__1(
    mut v_x_766_: *mut crate::leanh::LeanObject,
    mut v_a_767_: *mut crate::leanh::LeanObject,
    mut v_a_768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: u8 = 0;
    v___x_769_ = l_tactic_u220e___closed__1;
    v___x_770_ = l_Lean_Syntax_isOfKind(v_x_766_, v___x_769_);
    if v___x_770_ == 0 {
        let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_771_ = crate::leanh::lean_box(1);
        v___x_772_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_772_, 0, v___x_771_);
        crate::leanh::lean_ctor_set(v___x_772_, 1, v_a_768_);
        return v___x_772_;
    } else {
        let mut v_ref_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_774_: u8 = 0;
        let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_773_ = crate::leanh::lean_ctor_get(v_a_767_, 5);
        v___x_774_ = 0;
        v___x_775_ = l_Lean_SourceInfo_fromRef(v_ref_773_, v___x_774_);
        v___x_776_ = l_Lean_Parser_Tactic_tryTrace___closed__4;
        v___x_777_ = l_Lean_Parser_Tactic_tryTrace___closed__7;
        crate::leanh::lean_inc_n(v___x_775_, 3);
        v___x_778_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_778_, 0, v___x_775_);
        crate::leanh::lean_ctor_set(v___x_778_, 1, v___x_777_);
        v___x_779_ = l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1;
        v___x_780_ = l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3;
        v___x_781_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4_once
            ),
            _init_l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4,
        );
        v___x_782_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_782_, 0, v___x_775_);
        crate::leanh::lean_ctor_set(v___x_782_, 1, v___x_780_);
        crate::leanh::lean_ctor_set(v___x_782_, 2, v___x_781_);
        v___x_783_ = l_Lean_Syntax_node1(v___x_775_, v___x_779_, v___x_782_);
        v___x_784_ = l_Lean_Syntax_node2(v___x_775_, v___x_776_, v___x_778_, v___x_783_);
        v___x_785_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_785_, 0, v___x_784_);
        crate::leanh::lean_ctor_set(v___x_785_, 1, v_a_768_);
        return v___x_785_;
    }
}
pub unsafe fn l___aux__Init__Try______macroRules__tactic_u220e__1___boxed(
    mut v_x_786_: *mut crate::leanh::LeanObject,
    mut v_a_787_: *mut crate::leanh::LeanObject,
    mut v_a_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_789_ = l___aux__Init__Try______macroRules__tactic_u220e__1(v_x_786_, v_a_787_, v_a_788_);
    crate::leanh::lean_dec_ref(v_a_787_);
    return v_res_789_;
}
pub unsafe fn _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__11;
    v___x_833_ = l_String_toRawSubstring_x27(v___x_832_);
    return v___x_833_;
}
pub unsafe fn _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_837_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__14;
    v___x_838_ = l_String_toRawSubstring_x27(v___x_837_);
    return v___x_838_;
}
pub unsafe fn l___aux__Init__Try______macroRules__term_u220e__1(
    mut v_x_851_: *mut crate::leanh::LeanObject,
    mut v_a_852_: *mut crate::leanh::LeanObject,
    mut v_a_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    v___x_854_ = l_term_u220e___closed__1;
    v___x_855_ = l_Lean_Syntax_isOfKind(v_x_851_, v___x_854_);
    if v___x_855_ == 0 {
        let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_856_ = crate::leanh::lean_box(1);
        v___x_857_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_857_, 0, v___x_856_);
        crate::leanh::lean_ctor_set(v___x_857_, 1, v_a_853_);
        return v___x_857_;
    } else {
        let mut v_quotContext_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_861_: u8 = 0;
        let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_858_ = crate::leanh::lean_ctor_get(v_a_852_, 1);
        v_currMacroScope_859_ = crate::leanh::lean_ctor_get(v_a_852_, 2);
        v_ref_860_ = crate::leanh::lean_ctor_get(v_a_852_, 5);
        v___x_861_ = 0;
        v___x_862_ = l_Lean_SourceInfo_fromRef(v_ref_860_, v___x_861_);
        v___x_863_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__2;
        v___x_864_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__3;
        crate::leanh::lean_inc_n(v___x_862_, 15);
        v___x_865_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_865_, 0, v___x_862_);
        crate::leanh::lean_ctor_set(v___x_865_, 1, v___x_864_);
        v___x_866_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__4;
        v___x_867_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__6;
        v___x_868_ = l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3;
        v___x_869_ = l_Lean_Parser_Tactic_tryTrace___closed__4;
        v___x_870_ = l_Lean_Parser_Tactic_tryTrace___closed__7;
        v___x_871_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_871_, 0, v___x_862_);
        crate::leanh::lean_ctor_set(v___x_871_, 1, v___x_870_);
        v___x_872_ = l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1;
        v___x_873_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__8;
        v___x_874_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__10;
        v___x_875_ = l_Lean_Parser_Command_registerTryTactic___closed__12;
        v___x_876_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_876_, 0, v___x_862_);
        crate::leanh::lean_ctor_set(v___x_876_, 1, v___x_875_);
        v___x_877_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l___aux__Init__Try______macroRules__term_u220e__1___closed__12),
            core::ptr::addr_of_mut!(
                l___aux__Init__Try______macroRules__term_u220e__1___closed__12_once
            ),
            _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__12,
        );
        v___x_878_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__13;
        crate::leanh::lean_inc_n(v_currMacroScope_859_, 2);
        crate::leanh::lean_inc_n(v_quotContext_858_, 2);
        v___x_879_ = l_Lean_addMacroScope(v_quotContext_858_, v___x_878_, v_currMacroScope_859_);
        v___x_880_ = crate::leanh::lean_box(0);
        v___x_881_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_881_, 0, v___x_862_);
        crate::leanh::lean_ctor_set(v___x_881_, 1, v___x_877_);
        crate::leanh::lean_ctor_set(v___x_881_, 2, v___x_879_);
        crate::leanh::lean_ctor_set(v___x_881_, 3, v___x_880_);
        v___x_882_ = l_Lean_Parser_Command_registerTryTactic___closed__17;
        v___x_883_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_883_, 0, v___x_862_);
        crate::leanh::lean_ctor_set(v___x_883_, 1, v___x_882_);
        v___x_884_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l___aux__Init__Try______macroRules__term_u220e__1___closed__15),
            core::ptr::addr_of_mut!(
                l___aux__Init__Try______macroRules__term_u220e__1___closed__15_once
            ),
            _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__15,
        );
        v___x_885_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__16;
        v___x_886_ = l_Lean_addMacroScope(v_quotContext_858_, v___x_885_, v_currMacroScope_859_);
        v___x_887_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__20;
        v___x_888_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_888_, 0, v___x_862_);
        crate::leanh::lean_ctor_set(v___x_888_, 1, v___x_884_);
        crate::leanh::lean_ctor_set(v___x_888_, 2, v___x_886_);
        crate::leanh::lean_ctor_set(v___x_888_, 3, v___x_887_);
        v___x_889_ = l_Lean_Parser_Command_registerTryTactic___closed__24;
        v___x_890_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_890_, 0, v___x_862_);
        crate::leanh::lean_ctor_set(v___x_890_, 1, v___x_889_);
        v___x_891_ = l_Lean_Syntax_node5(
            v___x_862_, v___x_874_, v___x_876_, v___x_881_, v___x_883_, v___x_888_, v___x_890_,
        );
        v___x_892_ = l_Lean_Syntax_node1(v___x_862_, v___x_873_, v___x_891_);
        v___x_893_ = l_Lean_Syntax_node1(v___x_862_, v___x_868_, v___x_892_);
        v___x_894_ = l_Lean_Syntax_node1(v___x_862_, v___x_872_, v___x_893_);
        v___x_895_ = l_Lean_Syntax_node2(v___x_862_, v___x_869_, v___x_871_, v___x_894_);
        v___x_896_ = l_Lean_Syntax_node1(v___x_862_, v___x_868_, v___x_895_);
        v___x_897_ = l_Lean_Syntax_node1(v___x_862_, v___x_867_, v___x_896_);
        v___x_898_ = l_Lean_Syntax_node1(v___x_862_, v___x_866_, v___x_897_);
        v___x_899_ = l_Lean_Syntax_node2(v___x_862_, v___x_863_, v___x_865_, v___x_898_);
        v___x_900_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_900_, 0, v___x_899_);
        crate::leanh::lean_ctor_set(v___x_900_, 1, v_a_853_);
        return v___x_900_;
    }
}
pub unsafe fn l___aux__Init__Try______macroRules__term_u220e__1___boxed(
    mut v_x_901_: *mut crate::leanh::LeanObject,
    mut v_a_902_: *mut crate::leanh::LeanObject,
    mut v_a_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l___aux__Init__Try______macroRules__term_u220e__1(v_x_901_, v_a_902_, v_a_903_);
    crate::leanh::lean_dec_ref(v_a_902_);
    return v_res_904_;
}
pub unsafe fn l_Lean_Try_Marker___redArg(
    mut v_a_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_905_);
    return v_a_905_;
}
pub unsafe fn l_Lean_Try_Marker___redArg___boxed(
    mut v_a_906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_907_ = l_Lean_Try_Marker___redArg(v_a_906_);
    crate::leanh::lean_dec(v_a_906_);
    return v_res_907_;
}
pub unsafe fn l_Lean_Try_Marker(
    mut v_00_u03b1_908_: *mut crate::leanh::LeanObject,
    mut v_a_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_909_);
    return v_a_909_;
}
pub unsafe fn l_Lean_Try_Marker___boxed(
    mut v_00_u03b1_910_: *mut crate::leanh::LeanObject,
    mut v_a_911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_912_ = l_Lean_Try_Marker(v_00_u03b1_910_, v_a_911_);
    crate::leanh::lean_dec(v_a_911_);
    return v_res_912_;
}
pub unsafe fn l_Lean_Try_markerUnexpander___redArg(
    mut v_a_913_: *mut crate::leanh::LeanObject,
    mut v_a_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_915_: u8 = 0;
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_915_ = 0;
    v___x_916_ = l_Lean_SourceInfo_fromRef(v_a_913_, v___x_915_);
    v___x_917_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__2;
    v___x_918_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__3;
    crate::leanh::lean_inc_n(v___x_916_, 8);
    v___x_919_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_916_);
    crate::leanh::lean_ctor_set(v___x_919_, 1, v___x_918_);
    v___x_920_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__4;
    v___x_921_ = l___aux__Init__Try______macroRules__term_u220e__1___closed__6;
    v___x_922_ = l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3;
    v___x_923_ = l_Lean_Parser_Tactic_tryTrace___closed__4;
    v___x_924_ = l_Lean_Parser_Tactic_tryTrace___closed__7;
    v___x_925_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_925_, 0, v___x_916_);
    crate::leanh::lean_ctor_set(v___x_925_, 1, v___x_924_);
    v___x_926_ = l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1;
    v___x_927_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4),
        core::ptr::addr_of_mut!(
            l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4_once
        ),
        _init_l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4,
    );
    v___x_928_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_928_, 0, v___x_916_);
    crate::leanh::lean_ctor_set(v___x_928_, 1, v___x_922_);
    crate::leanh::lean_ctor_set(v___x_928_, 2, v___x_927_);
    v___x_929_ = l_Lean_Syntax_node1(v___x_916_, v___x_926_, v___x_928_);
    v___x_930_ = l_Lean_Syntax_node2(v___x_916_, v___x_923_, v___x_925_, v___x_929_);
    v___x_931_ = l_Lean_Syntax_node1(v___x_916_, v___x_922_, v___x_930_);
    v___x_932_ = l_Lean_Syntax_node1(v___x_916_, v___x_921_, v___x_931_);
    v___x_933_ = l_Lean_Syntax_node1(v___x_916_, v___x_920_, v___x_932_);
    v___x_934_ = l_Lean_Syntax_node2(v___x_916_, v___x_917_, v___x_919_, v___x_933_);
    v___x_935_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_935_, 0, v___x_934_);
    crate::leanh::lean_ctor_set(v___x_935_, 1, v_a_914_);
    return v___x_935_;
}
pub unsafe fn l_Lean_Try_markerUnexpander___redArg___boxed(
    mut v_a_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_Try_markerUnexpander___redArg(v_a_936_, v_a_937_);
    crate::leanh::lean_dec(v_a_936_);
    return v_res_938_;
}
pub unsafe fn l_Lean_Try_markerUnexpander(
    mut v_x_939_: *mut crate::leanh::LeanObject,
    mut v_a_940_: *mut crate::leanh::LeanObject,
    mut v_a_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_942_ = l_Lean_Try_markerUnexpander___redArg(v_a_940_, v_a_941_);
    return v___x_942_;
}
pub unsafe fn l_Lean_Try_markerUnexpander___boxed(
    mut v_x_943_: *mut crate::leanh::LeanObject,
    mut v_a_944_: *mut crate::leanh::LeanObject,
    mut v_a_945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_946_ = l_Lean_Try_markerUnexpander(v_x_943_, v_a_944_, v_a_945_);
    crate::leanh::lean_dec(v_a_944_);
    crate::leanh::lean_dec(v_x_943_);
    return v_res_946_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Try(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Try(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Tactic_tryTrace = _init_l_Lean_Parser_Tactic_tryTrace();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_tryTrace);
    l_Lean_Parser_Tactic_tryTraceWith = _init_l_Lean_Parser_Tactic_tryTraceWith();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_tryTraceWith);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Try(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Try(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Try(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Try(builtin);
}
