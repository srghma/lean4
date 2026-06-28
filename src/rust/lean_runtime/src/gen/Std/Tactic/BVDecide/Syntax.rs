// Lean compiler output
// Module: Std.Tactic.BVDecide.Syntax
// Imports: Init.Simproc Init.Grind.Tactics Init.MetaTypes Init.Data.Nat.Bitwise.Basic
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::MetaTypes::{initialize_Init_MetaTypes, runtime_initialize_Init_MetaTypes};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node5, l_Lean_Syntax_node8,
};
use crate::r#gen::Init::Simproc::{initialize_Init_Simproc, runtime_initialize_Init_Simproc};
use crate::r#gen::Init::Tactics::{
    l_Lean_Parser_Tactic_optConfig, l_Lean_Parser_Tactic_simpPost, l_Lean_Parser_Tactic_simpPre,
};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
pub static l_Lean_Parser_Tactic_bvCheck___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_bvCheck___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvCheck___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Tactic_bvCheck___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvCheck___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Tactic_bvCheck___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvCheck___closed__3_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [98, 118, 67, 104, 101, 99, 107, 0],
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_bvCheck___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__3_value)
                as *mut crate::leanh::LeanObject,
            6595225419433550061 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvCheck___closed__5_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lean_Parser_Tactic_bvCheck___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvCheck___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__5_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvCheck___closed__7_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [98, 118, 95, 99, 104, 101, 99, 107, 32, 0],
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvCheck___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__7_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_bvCheck___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_bvCheck___closed__10_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [115, 116, 114, 0],
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvCheck___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__10_value)
                as *mut crate::leanh::LeanObject,
            9232979286016572671 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvCheck___closed__12_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_bvCheck___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_bvCheck___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_bvCheck___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_bvCheck: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_bvDecide___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [98, 118, 68, 101, 99, 105, 100, 101, 0],
    };
static mut l_Lean_Parser_Tactic_bvDecide___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvDecide___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_bvDecide___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvDecide___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvDecide___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5664884566237612082 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvDecide___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvDecide___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvDecide___closed__2_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [98, 118, 95, 100, 101, 99, 105, 100, 101, 0],
    };
static mut l_Lean_Parser_Tactic_bvDecide___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvDecide___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvDecide___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvDecide___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvDecide___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvDecide___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_bvDecide___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_bvDecide___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_bvDecide___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_bvDecide___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_bvDecide: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_bvTrace___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [98, 118, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_bvTrace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvTrace___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_bvTrace___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvTrace___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10563082290425751099 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvTrace___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvTrace___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvTrace___closed__2_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [98, 118, 95, 100, 101, 99, 105, 100, 101, 63, 0],
    };
static mut l_Lean_Parser_Tactic_bvTrace___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvTrace___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvTrace___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvTrace___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvTrace___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_bvTrace___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_bvTrace___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_bvTrace___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_bvTrace___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_bvTrace: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_bvNormalize___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [98, 118, 78, 111, 114, 109, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Parser_Tactic_bvNormalize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_bvNormalize___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9992359010160305136 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvNormalize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvNormalize___closed__2_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [98, 118, 95, 110, 111, 114, 109, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Parser_Tactic_bvNormalize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_bvNormalize___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_bvNormalize___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_bvNormalize___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_bvNormalize___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_bvNormalize___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_bvNormalize___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_bvNormalize: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Parser_bv__normalize___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_bv__normalize___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_bv__normalize___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__0_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__2_value)
                as *mut crate::leanh::LeanObject,
            13147606709761642591 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__1_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lean_Parser_bv__normalize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__3_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lean_Parser_bv__normalize___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__3_value)
                as *mut crate::leanh::LeanObject,
            393173242845875278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_bv__normalize___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_bv__normalize___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_bv__normalize___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_bv__normalize___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_bv__normalize___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_bv__normalize___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_bv__normalize___closed__8_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 2,
        m_data: [226, 134, 144, 32, 0],
    };
static mut l_Lean_Parser_bv__normalize___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__9_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [60, 45, 32, 0],
    };
static mut l_Lean_Parser_bv__normalize___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 12,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__9_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__11_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_bv__normalize___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_bv__normalize___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_bv__normalize___closed__13_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 112, 83, 112, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_bv__normalize___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__13_value)
                as *mut crate::leanh::LeanObject,
            17761616517784022991 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__15_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__16_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [112, 114, 105, 111, 0],
    };
static mut l_Lean_Parser_bv__normalize___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__16_value)
                as *mut crate::leanh::LeanObject,
            17836958171642591098 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__18_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__17_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bv__normalize___closed__20_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_bv__normalize___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bv__normalize___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_bv__normalize___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_bv__normalize___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_bv__normalize___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_bv__normalize___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_bv__normalize: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__0_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        98, 118, 78, 111, 114, 109, 97, 108, 105, 122, 101, 80, 114, 111, 99, 66, 117, 105, 108,
        116, 105, 110, 65, 116, 116, 114, 0,
    ],
};
static mut l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13208588183044822389 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        98, 117, 105, 108, 116, 105, 110, 95, 98, 118, 95, 110, 111, 114, 109, 97, 108, 105, 122,
        101, 95, 112, 114, 111, 99, 0,
    ],
};
static mut l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_bvNormalizeProcBuiltinAttr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 66, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 95, 91, 95, 93, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__1_value) as *mut crate::leanh::LeanObject,12128620401598718473 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__3_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__6_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,11509420844586769999 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__10_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__11_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvNormalize___closed__2_value) as *mut crate::leanh::LeanObject,15275213774519138923 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__14_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__14_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__16_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__18_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 66, 117, 105, 108, 116, 105, 110, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__18_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__18_value) as *mut crate::leanh::LeanObject,14561357251485234313 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__22_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__22_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__22_value) as *mut crate::leanh::LeanObject,7983999284776576032 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__24_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0]};
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__24_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_bvCheck___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__24_value) as *mut crate::leanh::LeanObject,9063780239635860524 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx(
    mut v_x_437_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_437_ {
        0 => {
            let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_438_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_438_;
        }
        1 => {
            let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_439_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_439_;
        }
        _ => {
            let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_440_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_440_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx___boxed(
    mut v_x_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_442_: u8 = 0;
    let mut v_res_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_442_ = (crate::leanh::lean_unbox(v_x_441_) as u8);
    v_res_443_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx(v_x_boxed_442_);
    return v_res_443_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_toCtorIdx(
    mut v_x_444_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorIdx(v_x_444_);
    return v___x_445_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_toCtorIdx___boxed(
    mut v_x_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_447_: u8 = 0;
    let mut v_res_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_447_ = (crate::leanh::lean_unbox(v_x_446_) as u8);
    v_res_448_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_toCtorIdx(v_x_4__boxed_447_);
    return v_res_448_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg(
    mut v_k_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_449_);
    return v_k_449_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg___boxed(
    mut v_k_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_451_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___redArg(v_k_450_);
    crate::leanh::lean_dec(v_k_450_);
    return v_res_451_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim(
    mut v_motive_452_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_453_: *mut crate::leanh::LeanObject,
    mut v_t_454_: u8,
    mut v_h_455_: *mut crate::leanh::LeanObject,
    mut v_k_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_456_);
    return v_k_456_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim___boxed(
    mut v_motive_457_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_458_: *mut crate::leanh::LeanObject,
    mut v_t_459_: *mut crate::leanh::LeanObject,
    mut v_h_460_: *mut crate::leanh::LeanObject,
    mut v_k_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_462_: u8 = 0;
    let mut v_res_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_462_ = (crate::leanh::lean_unbox(v_t_459_) as u8);
    v_res_463_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_ctorElim(
        v_motive_457_,
        v_ctorIdx_458_,
        v_t_boxed_462_,
        v_h_460_,
        v_k_461_,
    );
    crate::leanh::lean_dec(v_k_461_);
    crate::leanh::lean_dec(v_ctorIdx_458_);
    return v_res_463_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg(
    mut v_proof_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_proof_464_);
    return v_proof_464_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg___boxed(
    mut v_proof_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_466_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___redArg(v_proof_465_);
    crate::leanh::lean_dec(v_proof_465_);
    return v_res_466_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim(
    mut v_motive_467_: *mut crate::leanh::LeanObject,
    mut v_t_468_: u8,
    mut v_h_469_: *mut crate::leanh::LeanObject,
    mut v_proof_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_proof_470_);
    return v_proof_470_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim___boxed(
    mut v_motive_471_: *mut crate::leanh::LeanObject,
    mut v_t_472_: *mut crate::leanh::LeanObject,
    mut v_h_473_: *mut crate::leanh::LeanObject,
    mut v_proof_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_475_: u8 = 0;
    let mut v_res_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_475_ = (crate::leanh::lean_unbox(v_t_472_) as u8);
    v_res_476_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_proof_elim(
        v_motive_471_,
        v_t_boxed_475_,
        v_h_473_,
        v_proof_474_,
    );
    crate::leanh::lean_dec(v_proof_474_);
    return v_res_476_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg(
    mut v_counterexample_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_counterexample_477_);
    return v_counterexample_477_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg___boxed(
    mut v_counterexample_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_479_ =
        l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___redArg(v_counterexample_478_);
    crate::leanh::lean_dec(v_counterexample_478_);
    return v_res_479_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim(
    mut v_motive_480_: *mut crate::leanh::LeanObject,
    mut v_t_481_: u8,
    mut v_h_482_: *mut crate::leanh::LeanObject,
    mut v_counterexample_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_counterexample_483_);
    return v_counterexample_483_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim___boxed(
    mut v_motive_484_: *mut crate::leanh::LeanObject,
    mut v_t_485_: *mut crate::leanh::LeanObject,
    mut v_h_486_: *mut crate::leanh::LeanObject,
    mut v_counterexample_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_488_: u8 = 0;
    let mut v_res_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_488_ = (crate::leanh::lean_unbox(v_t_485_) as u8);
    v_res_489_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_counterexample_elim(
        v_motive_484_,
        v_t_boxed_488_,
        v_h_486_,
        v_counterexample_487_,
    );
    crate::leanh::lean_dec(v_counterexample_487_);
    return v_res_489_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg(
    mut v_default_490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_default_490_);
    return v_default_490_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg___boxed(
    mut v_default_491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_492_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___redArg(v_default_491_);
    crate::leanh::lean_dec(v_default_491_);
    return v_res_492_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim(
    mut v_motive_493_: *mut crate::leanh::LeanObject,
    mut v_t_494_: u8,
    mut v_h_495_: *mut crate::leanh::LeanObject,
    mut v_default_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_default_496_);
    return v_default_496_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim___boxed(
    mut v_motive_497_: *mut crate::leanh::LeanObject,
    mut v_t_498_: *mut crate::leanh::LeanObject,
    mut v_h_499_: *mut crate::leanh::LeanObject,
    mut v_default_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_501_: u8 = 0;
    let mut v_res_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_501_ = (crate::leanh::lean_unbox(v_t_498_) as u8);
    v_res_502_ = l_Lean_Elab_Tactic_BVDecide_SolverMode_default_elim(
        v_motive_497_,
        v_t_boxed_501_,
        v_h_499_,
        v_default_500_,
    );
    crate::leanh::lean_dec(v_default_500_);
    return v_res_502_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvCheck___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_519_ = l_Lean_Parser_Tactic_optConfig;
    v___x_520_ = l_Lean_Parser_Tactic_bvCheck___closed__8;
    v___x_521_ = l_Lean_Parser_Tactic_bvCheck___closed__6;
    v___x_522_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_522_, 0, v___x_521_);
    crate::leanh::lean_ctor_set(v___x_522_, 1, v___x_520_);
    crate::leanh::lean_ctor_set(v___x_522_, 2, v___x_519_);
    return v___x_522_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvCheck___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_528_ = l_Lean_Parser_Tactic_bvCheck___closed__12;
    v___x_529_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvCheck___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvCheck___closed__9_once),
        _init_l_Lean_Parser_Tactic_bvCheck___closed__9,
    );
    v___x_530_ = l_Lean_Parser_Tactic_bvCheck___closed__6;
    v___x_531_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_531_, 0, v___x_530_);
    crate::leanh::lean_ctor_set(v___x_531_, 1, v___x_529_);
    crate::leanh::lean_ctor_set(v___x_531_, 2, v___x_528_);
    return v___x_531_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvCheck___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_532_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvCheck___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvCheck___closed__13_once),
        _init_l_Lean_Parser_Tactic_bvCheck___closed__13,
    );
    v___x_533_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_534_ = l_Lean_Parser_Tactic_bvCheck___closed__4;
    v___x_535_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_535_, 0, v___x_534_);
    crate::leanh::lean_ctor_set(v___x_535_, 1, v___x_533_);
    crate::leanh::lean_ctor_set(v___x_535_, 2, v___x_532_);
    return v___x_535_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvCheck() -> *mut crate::leanh::LeanObject {
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_536_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvCheck___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvCheck___closed__14_once),
        _init_l_Lean_Parser_Tactic_bvCheck___closed__14,
    );
    return v___x_536_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvDecide___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = l_Lean_Parser_Tactic_optConfig;
    v___x_548_ = l_Lean_Parser_Tactic_bvDecide___closed__3;
    v___x_549_ = l_Lean_Parser_Tactic_bvCheck___closed__6;
    v___x_550_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_550_, 0, v___x_549_);
    crate::leanh::lean_ctor_set(v___x_550_, 1, v___x_548_);
    crate::leanh::lean_ctor_set(v___x_550_, 2, v___x_547_);
    return v___x_550_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvDecide___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvDecide___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvDecide___closed__4_once),
        _init_l_Lean_Parser_Tactic_bvDecide___closed__4,
    );
    v___x_552_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_553_ = l_Lean_Parser_Tactic_bvDecide___closed__1;
    v___x_554_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_554_, 0, v___x_553_);
    crate::leanh::lean_ctor_set(v___x_554_, 1, v___x_552_);
    crate::leanh::lean_ctor_set(v___x_554_, 2, v___x_551_);
    return v___x_554_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvDecide() -> *mut crate::leanh::LeanObject {
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvDecide___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvDecide___closed__5_once),
        _init_l_Lean_Parser_Tactic_bvDecide___closed__5,
    );
    return v___x_555_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvTrace___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = l_Lean_Parser_Tactic_optConfig;
    v___x_567_ = l_Lean_Parser_Tactic_bvTrace___closed__3;
    v___x_568_ = l_Lean_Parser_Tactic_bvCheck___closed__6;
    v___x_569_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_569_, 0, v___x_568_);
    crate::leanh::lean_ctor_set(v___x_569_, 1, v___x_567_);
    crate::leanh::lean_ctor_set(v___x_569_, 2, v___x_566_);
    return v___x_569_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvTrace___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_570_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvTrace___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvTrace___closed__4_once),
        _init_l_Lean_Parser_Tactic_bvTrace___closed__4,
    );
    v___x_571_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_572_ = l_Lean_Parser_Tactic_bvTrace___closed__1;
    v___x_573_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_573_, 0, v___x_572_);
    crate::leanh::lean_ctor_set(v___x_573_, 1, v___x_571_);
    crate::leanh::lean_ctor_set(v___x_573_, 2, v___x_570_);
    return v___x_573_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvTrace() -> *mut crate::leanh::LeanObject {
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvTrace___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvTrace___closed__5_once),
        _init_l_Lean_Parser_Tactic_bvTrace___closed__5,
    );
    return v___x_574_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvNormalize___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_585_ = l_Lean_Parser_Tactic_optConfig;
    v___x_586_ = l_Lean_Parser_Tactic_bvNormalize___closed__3;
    v___x_587_ = l_Lean_Parser_Tactic_bvCheck___closed__6;
    v___x_588_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_588_, 0, v___x_587_);
    crate::leanh::lean_ctor_set(v___x_588_, 1, v___x_586_);
    crate::leanh::lean_ctor_set(v___x_588_, 2, v___x_585_);
    return v___x_588_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvNormalize___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvNormalize___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvNormalize___closed__4_once),
        _init_l_Lean_Parser_Tactic_bvNormalize___closed__4,
    );
    v___x_590_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_591_ = l_Lean_Parser_Tactic_bvNormalize___closed__1;
    v___x_592_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_592_, 0, v___x_591_);
    crate::leanh::lean_ctor_set(v___x_592_, 1, v___x_590_);
    crate::leanh::lean_ctor_set(v___x_592_, 2, v___x_589_);
    return v___x_592_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_bvNormalize() -> *mut crate::leanh::LeanObject {
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_593_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvNormalize___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_bvNormalize___closed__5_once),
        _init_l_Lean_Parser_Tactic_bvNormalize___closed__5,
    );
    return v___x_593_;
}
pub unsafe fn _init_l_Lean_Parser_bv__normalize___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_604_ = l_Lean_Parser_Tactic_simpPost;
    v___x_605_ = l_Lean_Parser_Tactic_simpPre;
    v___x_606_ = l_Lean_Parser_bv__normalize___closed__4;
    v___x_607_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_607_, 0, v___x_606_);
    crate::leanh::lean_ctor_set(v___x_607_, 1, v___x_605_);
    crate::leanh::lean_ctor_set(v___x_607_, 2, v___x_604_);
    return v___x_607_;
}
pub unsafe fn _init_l_Lean_Parser_bv__normalize___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__5_once),
        _init_l_Lean_Parser_bv__normalize___closed__5,
    );
    v___x_609_ = l_Lean_Parser_bv__normalize___closed__2;
    v___x_610_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_610_, 0, v___x_609_);
    crate::leanh::lean_ctor_set(v___x_610_, 1, v___x_608_);
    return v___x_610_;
}
pub unsafe fn _init_l_Lean_Parser_bv__normalize___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_611_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__6_once),
        _init_l_Lean_Parser_bv__normalize___closed__6,
    );
    v___x_612_ = l_Lean_Parser_Tactic_bvNormalize___closed__3;
    v___x_613_ = l_Lean_Parser_Tactic_bvCheck___closed__6;
    v___x_614_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_614_, 0, v___x_613_);
    crate::leanh::lean_ctor_set(v___x_614_, 1, v___x_612_);
    crate::leanh::lean_ctor_set(v___x_614_, 2, v___x_611_);
    return v___x_614_;
}
pub unsafe fn _init_l_Lean_Parser_bv__normalize___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_624_ = l_Lean_Parser_bv__normalize___closed__11;
    v___x_625_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__7_once),
        _init_l_Lean_Parser_bv__normalize___closed__7,
    );
    v___x_626_ = l_Lean_Parser_Tactic_bvCheck___closed__6;
    v___x_627_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_627_, 0, v___x_626_);
    crate::leanh::lean_ctor_set(v___x_627_, 1, v___x_625_);
    crate::leanh::lean_ctor_set(v___x_627_, 2, v___x_624_);
    return v___x_627_;
}
pub unsafe fn _init_l_Lean_Parser_bv__normalize___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ = l_Lean_Parser_bv__normalize___closed__20;
    v___x_647_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__12_once),
        _init_l_Lean_Parser_bv__normalize___closed__12,
    );
    v___x_648_ = l_Lean_Parser_Tactic_bvCheck___closed__6;
    v___x_649_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_649_, 0, v___x_648_);
    crate::leanh::lean_ctor_set(v___x_649_, 1, v___x_647_);
    crate::leanh::lean_ctor_set(v___x_649_, 2, v___x_646_);
    return v___x_649_;
}
pub unsafe fn _init_l_Lean_Parser_bv__normalize___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__21_once),
        _init_l_Lean_Parser_bv__normalize___closed__21,
    );
    v___x_651_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_652_ = l_Lean_Parser_bv__normalize___closed__0;
    v___x_653_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_653_, 0, v___x_652_);
    crate::leanh::lean_ctor_set(v___x_653_, 1, v___x_651_);
    crate::leanh::lean_ctor_set(v___x_653_, 2, v___x_650_);
    return v___x_653_;
}
pub unsafe fn _init_l_Lean_Parser_bv__normalize() -> *mut crate::leanh::LeanObject {
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_654_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__22_once),
        _init_l_Lean_Parser_bv__normalize___closed__22,
    );
    return v___x_654_;
}
pub unsafe fn _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_664_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_bv__normalize___closed__6_once),
        _init_l_Lean_Parser_bv__normalize___closed__6,
    );
    v___x_665_ = l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__3;
    v___x_666_ = l_Lean_Parser_Tactic_bvCheck___closed__6;
    v___x_667_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_667_, 0, v___x_666_);
    crate::leanh::lean_ctor_set(v___x_667_, 1, v___x_665_);
    crate::leanh::lean_ctor_set(v___x_667_, 2, v___x_664_);
    return v___x_667_;
}
pub unsafe fn _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4_once),
        _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__4,
    );
    v___x_669_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_670_ = l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1;
    v___x_671_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_671_, 0, v___x_670_);
    crate::leanh::lean_ctor_set(v___x_671_, 1, v___x_669_);
    crate::leanh::lean_ctor_set(v___x_671_, 2, v___x_668_);
    return v___x_671_;
}
pub unsafe fn _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr() -> *mut crate::leanh::LeanObject {
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_672_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5_once),
        _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__5,
    );
    return v___x_672_;
}
pub unsafe fn _init_l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_707_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_707_;
}
pub unsafe fn l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(
    mut v_x_721_: *mut crate::leanh::LeanObject,
    mut v_a_722_: *mut crate::leanh::LeanObject,
    mut v_a_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: u8 = 0;
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: u8 = 0;
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: u8 = 0;
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: u8 = 0;
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: u8 = 0;
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: u8 = 0;
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_x3f_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: u8 = 0;
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: u8 = 0;
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: u8 = 0;
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_750_ = l_Lean_Parser_Tactic_bvCheck___closed__0;
                v___x_751_ = l_Lean_Parser_Tactic_bvCheck___closed__1;
                v___x_752_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__2;
                crate::leanh::lean_inc(v_x_721_);
                v___x_753_ = l_Lean_Syntax_isOfKind(v_x_721_, v___x_752_);
                if v___x_753_ == 0 {
                    crate::leanh::lean_dec(v_x_721_);
                    v___x_754_ = crate::leanh::lean_box(1);
                    v___x_755_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_755_, 0, v___x_754_);
                    crate::leanh::lean_ctor_set(v___x_755_, 1, v_a_723_);
                    return v___x_755_;
                } else {
                    v___x_756_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_856_ = l_Lean_Syntax_getArg(v_x_721_, v___x_756_);
                    v___x_857_ = l_Lean_Syntax_isNone(v___x_856_);
                    if v___x_857_ == 0 {
                        v___x_858_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_856_);
                        v___x_859_ = l_Lean_Syntax_matchesNull(v___x_856_, v___x_858_);
                        if v___x_859_ == 0 {
                            crate::leanh::lean_dec(v___x_856_);
                            crate::leanh::lean_dec(v_x_721_);
                            v___x_860_ = crate::leanh::lean_box(1);
                            v___x_861_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_861_, 0, v___x_860_);
                            crate::leanh::lean_ctor_set(v___x_861_, 1, v_a_723_);
                            return v___x_861_;
                        } else {
                            v_doc_x3f_862_ = l_Lean_Syntax_getArg(v___x_856_, v___x_756_);
                            crate::leanh::lean_dec(v___x_856_);
                            v___x_863_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__25;
                            crate::leanh::lean_inc(v_doc_x3f_862_);
                            v___x_864_ = l_Lean_Syntax_isOfKind(v_doc_x3f_862_, v___x_863_);
                            if v___x_864_ == 0 {
                                crate::leanh::lean_dec(v_doc_x3f_862_);
                                crate::leanh::lean_dec(v_x_721_);
                                v___x_865_ = crate::leanh::lean_box(1);
                                v___x_866_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_866_, 0, v___x_865_);
                                crate::leanh::lean_ctor_set(v___x_866_, 1, v_a_723_);
                                return v___x_866_;
                            } else {
                                v___x_867_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_867_, 0, v_doc_x3f_862_);
                                v_doc_x3f_837_ = v___x_867_;
                                v___y_838_ = v_a_722_;
                                v___y_839_ = v_a_723_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_856_);
                        v___x_868_ = crate::leanh::lean_box(0);
                        v_doc_x3f_837_ = v___x_868_;
                        v___y_838_ = v_a_722_;
                        v___y_839_ = v_a_723_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_726_);
                v___x_739_ = l_Array_append___redArg(v___y_726_, v___y_738_);
                crate::leanh::lean_dec_ref(v___y_738_);
                crate::leanh::lean_inc_n(v___y_733_, 4);
                crate::leanh::lean_inc_n(v___y_735_, 7);
                v___x_740_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_740_, 0, v___y_735_);
                crate::leanh::lean_ctor_set(v___x_740_, 1, v___y_733_);
                crate::leanh::lean_ctor_set(v___x_740_, 2, v___x_739_);
                crate::leanh::lean_inc(v___y_727_);
                v___x_741_ = l_Lean_Syntax_node2(v___y_735_, v___y_727_, v___y_736_, v___x_740_);
                v___x_742_ = l_Lean_Syntax_node2(v___y_735_, v___y_729_, v___y_734_, v___x_741_);
                v___x_743_ = l_Lean_Syntax_node1(v___y_735_, v___y_733_, v___x_742_);
                v___x_744_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__0;
                v___x_745_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_745_, 0, v___y_735_);
                crate::leanh::lean_ctor_set(v___x_745_, 1, v___x_744_);
                v___x_746_ = l_Lean_Syntax_node1(v___y_735_, v___y_733_, v___y_725_);
                crate::leanh::lean_inc(v___y_737_);
                v___x_747_ = l_Lean_Syntax_node5(
                    v___y_735_, v___y_737_, v___y_730_, v___y_728_, v___x_743_, v___x_745_,
                    v___x_746_,
                );
                v___x_748_ = l_Lean_Syntax_node2(v___y_735_, v___y_733_, v___y_732_, v___x_747_);
                v___x_749_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_749_, 0, v___x_748_);
                crate::leanh::lean_ctor_set(v___x_749_, 1, v___y_731_);
                return v___x_749_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_760_);
                v___x_770_ = l_Array_append___redArg(v___y_760_, v___y_769_);
                crate::leanh::lean_dec_ref(v___y_769_);
                crate::leanh::lean_inc(v___y_764_);
                crate::leanh::lean_inc_n(v___y_766_, 9);
                v___x_771_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_771_, 0, v___y_766_);
                crate::leanh::lean_ctor_set(v___x_771_, 1, v___y_764_);
                crate::leanh::lean_ctor_set(v___x_771_, 2, v___x_770_);
                v___x_772_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__3;
                v___x_773_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_773_, 0, v___y_766_);
                crate::leanh::lean_ctor_set(v___x_773_, 1, v___x_772_);
                v___x_774_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__4;
                v___x_775_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_775_, 0, v___y_766_);
                crate::leanh::lean_ctor_set(v___x_775_, 1, v___x_774_);
                v___x_776_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__5;
                v___x_777_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_777_, 0, v___y_766_);
                crate::leanh::lean_ctor_set(v___x_777_, 1, v___x_776_);
                v___x_778_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__6;
                v___x_779_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_779_, 0, v___y_766_);
                crate::leanh::lean_ctor_set(v___x_779_, 1, v___x_778_);
                crate::leanh::lean_inc(v___y_759_);
                crate::leanh::lean_inc(v___y_768_);
                v___x_780_ = l_Lean_Syntax_node8(
                    v___y_766_, v___y_768_, v___x_771_, v___x_773_, v___y_759_, v___x_775_,
                    v___y_758_, v___x_777_, v___x_779_, v___y_761_,
                );
                v___x_781_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__8;
                v___x_782_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__9;
                v___x_783_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_783_, 0, v___y_766_);
                crate::leanh::lean_ctor_set(v___x_783_, 1, v___x_781_);
                v___x_784_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__10;
                v___x_785_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_785_, 0, v___y_766_);
                crate::leanh::lean_ctor_set(v___x_785_, 1, v___x_784_);
                v___x_786_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__11;
                crate::leanh::lean_inc_ref(v___y_762_);
                v___x_787_ = l_Lean_Name_mkStr4(v___x_750_, v___x_751_, v___y_762_, v___x_786_);
                v___x_788_ = l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__1;
                v___x_789_ = l_Lean_Parser_bvNormalizeProcBuiltinAttr___closed__2;
                v___x_790_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_790_, 0, v___y_766_);
                crate::leanh::lean_ctor_set(v___x_790_, 1, v___x_789_);
                if crate::leanh::lean_obj_tag(v___y_767_) == 1 {
                    v_val_791_ = crate::leanh::lean_ctor_get(v___y_767_, 0);
                    crate::leanh::lean_inc(v_val_791_);
                    crate::leanh::lean_dec_ref_known(v___y_767_, 1);
                    v___x_792_ = l_Array_mkArray1___redArg(v_val_791_);
                    v___y_725_ = v___y_759_;
                    v___y_726_ = v___y_760_;
                    v___y_727_ = v___x_788_;
                    v___y_728_ = v___x_785_;
                    v___y_729_ = v___x_787_;
                    v___y_730_ = v___x_783_;
                    v___y_731_ = v___y_765_;
                    v___y_732_ = v___x_780_;
                    v___y_733_ = v___y_764_;
                    v___y_734_ = v___y_763_;
                    v___y_735_ = v___y_766_;
                    v___y_736_ = v___x_790_;
                    v___y_737_ = v___x_782_;
                    v___y_738_ = v___x_792_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_767_);
                    v___x_793_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12;
                    v___y_725_ = v___y_759_;
                    v___y_726_ = v___y_760_;
                    v___y_727_ = v___x_788_;
                    v___y_728_ = v___x_785_;
                    v___y_729_ = v___x_787_;
                    v___y_730_ = v___x_783_;
                    v___y_731_ = v___y_765_;
                    v___y_732_ = v___x_780_;
                    v___y_733_ = v___y_764_;
                    v___y_734_ = v___y_763_;
                    v___y_735_ = v___y_766_;
                    v___y_736_ = v___x_790_;
                    v___y_737_ = v___x_782_;
                    v___y_738_ = v___x_793_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_803_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_804_ = l_Lean_Syntax_getArg(v_x_721_, v___x_803_);
                crate::leanh::lean_inc(v___x_804_);
                v___x_805_ = l_Lean_Syntax_matchesNull(v___x_804_, v___y_795_);
                if v___x_805_ == 0 {
                    crate::leanh::lean_dec(v___x_804_);
                    crate::leanh::lean_dec(v_pre_x3f_800_);
                    crate::leanh::lean_dec(v___y_798_);
                    crate::leanh::lean_dec(v___y_797_);
                    crate::leanh::lean_dec(v_x_721_);
                    v___x_806_ = crate::leanh::lean_box(1);
                    v___x_807_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_807_, 0, v___x_806_);
                    crate::leanh::lean_ctor_set(v___x_807_, 1, v___y_802_);
                    return v___x_807_;
                } else {
                    v___x_808_ = l_Lean_Syntax_getArg(v___x_804_, v___y_799_);
                    crate::leanh::lean_dec(v___x_804_);
                    crate::leanh::lean_inc(v___x_808_);
                    v___x_809_ = l_Lean_Syntax_matchesNull(v___x_808_, v___y_799_);
                    if v___x_809_ == 0 {
                        crate::leanh::lean_dec(v___x_808_);
                        crate::leanh::lean_dec(v_pre_x3f_800_);
                        crate::leanh::lean_dec(v___y_798_);
                        crate::leanh::lean_dec(v___y_797_);
                        crate::leanh::lean_dec(v_x_721_);
                        v___x_810_ = crate::leanh::lean_box(1);
                        v___x_811_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_811_, 0, v___x_810_);
                        crate::leanh::lean_ctor_set(v___x_811_, 1, v___y_802_);
                        return v___x_811_;
                    } else {
                        v___x_812_ = l_Lean_Syntax_getArg(v___x_808_, v___x_756_);
                        crate::leanh::lean_dec(v___x_808_);
                        v___x_813_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__13;
                        v___x_814_ = l_Lean_Syntax_matchesIdent(v___x_812_, v___x_813_);
                        crate::leanh::lean_dec(v___x_812_);
                        if v___x_814_ == 0 {
                            crate::leanh::lean_dec(v_pre_x3f_800_);
                            crate::leanh::lean_dec(v___y_798_);
                            crate::leanh::lean_dec(v___y_797_);
                            crate::leanh::lean_dec(v_x_721_);
                            v___x_815_ = crate::leanh::lean_box(1);
                            v___x_816_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_816_, 0, v___x_815_);
                            crate::leanh::lean_ctor_set(v___x_816_, 1, v___y_802_);
                            return v___x_816_;
                        } else {
                            v___x_817_ = crate::leanh::lean_unsigned_to_nat(5);
                            v___x_818_ = l_Lean_Syntax_getArg(v_x_721_, v___x_817_);
                            v___x_819_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__15;
                            crate::leanh::lean_inc(v___x_818_);
                            v___x_820_ = l_Lean_Syntax_isOfKind(v___x_818_, v___x_819_);
                            if v___x_820_ == 0 {
                                crate::leanh::lean_dec(v___x_818_);
                                crate::leanh::lean_dec(v_pre_x3f_800_);
                                crate::leanh::lean_dec(v___y_798_);
                                crate::leanh::lean_dec(v___y_797_);
                                crate::leanh::lean_dec(v_x_721_);
                                v___x_821_ = crate::leanh::lean_box(1);
                                v___x_822_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_822_, 0, v___x_821_);
                                crate::leanh::lean_ctor_set(v___x_822_, 1, v___y_802_);
                                return v___x_822_;
                            } else {
                                v_ref_823_ = crate::leanh::lean_ctor_get(v___y_801_, 5);
                                v___x_824_ = crate::leanh::lean_unsigned_to_nat(7);
                                v___x_825_ = l_Lean_Syntax_getArg(v_x_721_, v___x_824_);
                                v___x_826_ = crate::leanh::lean_unsigned_to_nat(10);
                                v___x_827_ = l_Lean_Syntax_getArg(v_x_721_, v___x_826_);
                                crate::leanh::lean_dec(v_x_721_);
                                v___x_828_ = 0;
                                v___x_829_ = l_Lean_SourceInfo_fromRef(v_ref_823_, v___x_828_);
                                v___x_830_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__17;
                                v___x_831_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__19;
                                v___x_832_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20_once), _init_l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__20);
                                if crate::leanh::lean_obj_tag(v___y_797_) == 1 {
                                    v_val_833_ = crate::leanh::lean_ctor_get(v___y_797_, 0);
                                    crate::leanh::lean_inc(v_val_833_);
                                    crate::leanh::lean_dec_ref_known(v___y_797_, 1);
                                    v___x_834_ = l_Array_mkArray1___redArg(v_val_833_);
                                    v___y_758_ = v___x_825_;
                                    v___y_759_ = v___x_818_;
                                    v___y_760_ = v___x_832_;
                                    v___y_761_ = v___x_827_;
                                    v___y_762_ = v___y_796_;
                                    v___y_763_ = v___y_798_;
                                    v___y_764_ = v___x_830_;
                                    v___y_765_ = v___y_802_;
                                    v___y_766_ = v___x_829_;
                                    v___y_767_ = v_pre_x3f_800_;
                                    v___y_768_ = v___x_831_;
                                    v___y_769_ = v___x_834_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___y_797_);
                                    v___x_835_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__12;
                                    v___y_758_ = v___x_825_;
                                    v___y_759_ = v___x_818_;
                                    v___y_760_ = v___x_832_;
                                    v___y_761_ = v___x_827_;
                                    v___y_762_ = v___y_796_;
                                    v___y_763_ = v___y_798_;
                                    v___y_764_ = v___x_830_;
                                    v___y_765_ = v___y_802_;
                                    v___y_766_ = v___x_829_;
                                    v___y_767_ = v_pre_x3f_800_;
                                    v___y_768_ = v___x_831_;
                                    v___y_769_ = v___x_835_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_840_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_841_ = l_Lean_Syntax_getArg(v_x_721_, v___x_840_);
                v___x_842_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__21;
                v___x_843_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___closed__23;
                crate::leanh::lean_inc(v___x_841_);
                v___x_844_ = l_Lean_Syntax_isOfKind(v___x_841_, v___x_843_);
                if v___x_844_ == 0 {
                    crate::leanh::lean_dec(v___x_841_);
                    crate::leanh::lean_dec(v_doc_x3f_837_);
                    crate::leanh::lean_dec(v_x_721_);
                    v___x_845_ = crate::leanh::lean_box(1);
                    v___x_846_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_846_, 0, v___x_845_);
                    crate::leanh::lean_ctor_set(v___x_846_, 1, v___y_839_);
                    return v___x_846_;
                } else {
                    v___x_847_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_848_ = l_Lean_Syntax_getArg(v_x_721_, v___x_847_);
                    v___x_849_ = l_Lean_Syntax_isNone(v___x_848_);
                    if v___x_849_ == 0 {
                        crate::leanh::lean_inc(v___x_848_);
                        v___x_850_ = l_Lean_Syntax_matchesNull(v___x_848_, v___x_840_);
                        if v___x_850_ == 0 {
                            crate::leanh::lean_dec(v___x_848_);
                            crate::leanh::lean_dec(v___x_841_);
                            crate::leanh::lean_dec(v_doc_x3f_837_);
                            crate::leanh::lean_dec(v_x_721_);
                            v___x_851_ = crate::leanh::lean_box(1);
                            v___x_852_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_852_, 0, v___x_851_);
                            crate::leanh::lean_ctor_set(v___x_852_, 1, v___y_839_);
                            return v___x_852_;
                        } else {
                            v_pre_x3f_853_ = l_Lean_Syntax_getArg(v___x_848_, v___x_756_);
                            crate::leanh::lean_dec(v___x_848_);
                            v___x_854_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_854_, 0, v_pre_x3f_853_);
                            v___y_795_ = v___x_847_;
                            v___y_796_ = v___x_842_;
                            v___y_797_ = v_doc_x3f_837_;
                            v___y_798_ = v___x_841_;
                            v___y_799_ = v___x_840_;
                            v_pre_x3f_800_ = v___x_854_;
                            v___y_801_ = v___y_838_;
                            v___y_802_ = v___y_839_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_848_);
                        v___x_855_ = crate::leanh::lean_box(0);
                        v___y_795_ = v___x_847_;
                        v___y_796_ = v___x_842_;
                        v___y_797_ = v_doc_x3f_837_;
                        v___y_798_ = v___x_841_;
                        v___y_799_ = v___x_840_;
                        v_pre_x3f_800_ = v___x_855_;
                        v___y_801_ = v___y_838_;
                        v___y_802_ = v___y_839_;
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1___boxed(
    mut v_x_869_: *mut crate::leanh::LeanObject,
    mut v_a_870_: *mut crate::leanh::LeanObject,
    mut v_a_871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_872_ = l_Lean_Parser___aux__Std__Tactic__BVDecide__Syntax______macroRules__Lean__Parser__command____Builtin__simproc_____x5b___x5d___x28___x29_x3a_x3d____1(v_x_869_, v_a_870_, v_a_871_);
    crate::leanh::lean_dec_ref(v_a_870_);
    return v_res_872_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Syntax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Syntax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Tactic_bvCheck = _init_l_Lean_Parser_Tactic_bvCheck();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_bvCheck);
    l_Lean_Parser_Tactic_bvDecide = _init_l_Lean_Parser_Tactic_bvDecide();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_bvDecide);
    l_Lean_Parser_Tactic_bvTrace = _init_l_Lean_Parser_Tactic_bvTrace();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_bvTrace);
    l_Lean_Parser_Tactic_bvNormalize = _init_l_Lean_Parser_Tactic_bvNormalize();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_bvNormalize);
    l_Lean_Parser_bv__normalize = _init_l_Lean_Parser_bv__normalize();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_bv__normalize);
    l_Lean_Parser_bvNormalizeProcBuiltinAttr = _init_l_Lean_Parser_bvNormalizeProcBuiltinAttr();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_bvNormalizeProcBuiltinAttr);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Syntax(builtin);
}
