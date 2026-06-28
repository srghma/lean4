// Lean compiler output
// Module: Init.Control.Basic
// Imports: Init.Core Init.BinderNameHint
use crate::r#gen::Init::BinderNameHint::{
    initialize_Init_BinderNameHint, runtime_initialize_Init_BinderNameHint,
};
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
pub static l_term___x3c_x26_x3e___00__closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 60, 38, 62, 95, 0],
    };
static mut l_term___x3c_x26_x3e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            17902794450874024165 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__2_value: crate::leanh::LeanStringObject<8> =
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
static mut l_term___x3c_x26_x3e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__4_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [32, 60, 38, 62, 32, 0],
    };
static mut l_term___x3c_x26_x3e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__6_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_term___x3c_x26_x3e___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            (((100 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__10_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((100 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((101 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term___x3c_x26_x3e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [70, 117, 110, 99, 116, 111, 114, 46, 109, 97, 112, 82, 101, 118, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [70, 117, 110, 99, 116, 111, 114, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 97, 112, 82, 101, 118, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value) as *mut crate::leanh::LeanObject,2226500928782199335 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value) as *mut crate::leanh::LeanObject,17798854418672644188 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_optional___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_optional___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_optional___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_optional___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToBoolBool___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToBoolBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToBoolBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToBoolBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToBoolBool: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToBoolBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 124, 124, 62, 95, 0],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            18177464721573610742 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [32, 60, 124, 124, 62, 32, 0],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__4_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            (((30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__6_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term___x3c_x7c_x7c_x3e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 114, 77, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value) as *mut crate::leanh::LeanObject,17806001628258047394 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 38, 38, 62, 95, 0],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            3935687535564439542 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [32, 60, 38, 38, 62, 32, 0],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__4_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            (((35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__6_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term___x3c_x26_x26_x3e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 110, 100, 77, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value) as *mut crate::leanh::LeanObject,8873471052530828183 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_instMonadControlTOfPure___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadControlTOfPure___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadControlTOfPure___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlTOfPure___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMonadControlTOfPure___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadControlTOfPure___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_instMonadControlTOfPure___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instMonadControlTOfPure___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlTOfPure___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 62, 61, 62, 95, 0],
    };
static mut l_term___x3e_x3d_x3e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            376317980966388524 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [32, 62, 61, 62, 32, 0],
    };
static mut l_term___x3e_x3d_x3e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__4_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            (((55 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__6_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((55 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((56 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term___x3e_x3d_x3e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [66, 105, 110, 100, 46, 107, 108, 101, 105, 115, 108, 105, 82, 105, 103, 104, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 105, 110, 100, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [107, 108, 101, 105, 115, 108, 105, 82, 105, 103, 104, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject,15820500991164727518 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value) as *mut crate::leanh::LeanObject,13518541916787333104 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 60, 61, 60, 95, 0],
    };
static mut l_term___x3c_x3d_x3c___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            6578201212627747956 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x3d_x3c___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [32, 60, 61, 60, 32, 0],
    };
static mut l_term___x3c_x3d_x3c___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x3d_x3c___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x3d_x3c___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((55 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((56 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x3d_x3c___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term___x3c_x3d_x3c__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [66, 105, 110, 100, 46, 107, 108, 101, 105, 115, 108, 105, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [107, 108, 101, 105, 115, 108, 105, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject,15820500991164727518 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject,2391163329140571260 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 61, 60, 60, 95, 0],
    };
static mut l_term___x3d_x3c_x3c___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            6202646376755925288 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3d_x3c_x3c___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [32, 61, 60, 60, 32, 0],
    };
static mut l_term___x3d_x3c_x3c___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3d_x3c_x3c___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3d_x3c_x3c___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((55 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((56 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term___x3d_x3c_x3c___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term___x3d_x3c_x3c__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [66, 105, 110, 100, 46, 98, 105, 110, 100, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 105, 110, 100, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject,15820500991164727518 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject,10226104227652591212 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_instForInOfForIn_x27___redArg___lam__0(
    mut v_f_860_: *mut crate::leanh::LeanObject,
    mut v_a_861_: *mut crate::leanh::LeanObject,
    mut v_x_862_: *mut crate::leanh::LeanObject,
    mut v___y_863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = crate::leanh::lean_apply_2(v_f_860_, v_a_861_, v___y_863_);
    return v___x_864_;
}
pub unsafe fn l_instForInOfForIn_x27___redArg___lam__1(
    mut v_inst_865_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_866_: *mut crate::leanh::LeanObject,
    mut v_x_867_: *mut crate::leanh::LeanObject,
    mut v_b_868_: *mut crate::leanh::LeanObject,
    mut v_f_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_870_ = crate::leanh::lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_870_, 0, v_f_869_);
    v___x_871_ = crate::leanh::lean_apply_4(
        v_inst_865_,
        crate::leanh::lean_box(0),
        v_x_867_,
        v_b_868_,
        v___f_870_,
    );
    return v___x_871_;
}
pub unsafe fn l_instForInOfForIn_x27___redArg(
    mut v_inst_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_873_ = crate::leanh::lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_873_, 0, v_inst_872_);
    return v___f_873_;
}
pub unsafe fn l_instForInOfForIn_x27(
    mut v_m_874_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_875_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_876_: *mut crate::leanh::LeanObject,
    mut v_d_877_: *mut crate::leanh::LeanObject,
    mut v_inst_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_879_ = crate::leanh::lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_879_, 0, v_inst_878_);
    return v___f_879_;
}
pub unsafe fn l_ForInStep_value___redArg(
    mut v_x_880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_881_ = crate::leanh::lean_ctor_get(v_x_880_, 0);
    crate::leanh::lean_inc(v_a_881_);
    return v_a_881_;
}
pub unsafe fn l_ForInStep_value___redArg___boxed(
    mut v_x_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_883_ = l_ForInStep_value___redArg(v_x_882_);
    crate::leanh::lean_dec_ref(v_x_882_);
    return v_res_883_;
}
pub unsafe fn l_ForInStep_value(
    mut v_00_u03b1_884_: *mut crate::leanh::LeanObject,
    mut v_x_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_886_ = crate::leanh::lean_ctor_get(v_x_885_, 0);
    crate::leanh::lean_inc(v_a_886_);
    return v_a_886_;
}
pub unsafe fn l_ForInStep_value___boxed(
    mut v_00_u03b1_887_: *mut crate::leanh::LeanObject,
    mut v_x_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_889_ = l_ForInStep_value(v_00_u03b1_887_, v_x_888_);
    crate::leanh::lean_dec_ref(v_x_888_);
    return v_res_889_;
}
pub unsafe fn l_Functor_mapRev___redArg(
    mut v_inst_890_: *mut crate::leanh::LeanObject,
    mut v_a_891_: *mut crate::leanh::LeanObject,
    mut v_f_892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_893_ = crate::leanh::lean_ctor_get(v_inst_890_, 0);
    crate::leanh::lean_inc(v_map_893_);
    crate::leanh::lean_dec_ref(v_inst_890_);
    v___x_894_ = crate::leanh::lean_apply_4(
        v_map_893_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_f_892_,
        v_a_891_,
    );
    return v___x_894_;
}
pub unsafe fn l_Functor_mapRev(
    mut v_f_895_: *mut crate::leanh::LeanObject,
    mut v_inst_896_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_897_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_898_: *mut crate::leanh::LeanObject,
    mut v_a_899_: *mut crate::leanh::LeanObject,
    mut v_f_900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_901_ = l_Functor_mapRev___redArg(v_inst_896_, v_a_899_, v_f_900_);
    return v___x_901_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_937_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5;
    v___x_938_ = l_String_toRawSubstring_x27(v___x_937_);
    return v___x_938_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1(
    mut v_x_953_: *mut crate::leanh::LeanObject,
    mut v_a_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u8 = 0;
    v___x_956_ = l_term___x3c_x26_x3e___00__closed__1;
    crate::leanh::lean_inc(v_x_953_);
    v___x_957_ = l_Lean_Syntax_isOfKind(v_x_953_, v___x_956_);
    if v___x_957_ == 0 {
        let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_953_);
        v___x_958_ = crate::leanh::lean_box(1);
        v___x_959_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_959_, 0, v___x_958_);
        crate::leanh::lean_ctor_set(v___x_959_, 1, v_a_955_);
        return v___x_959_;
    } else {
        let mut v_quotContext_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: u8 = 0;
        let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_960_ = crate::leanh::lean_ctor_get(v_a_954_, 1);
        v_currMacroScope_961_ = crate::leanh::lean_ctor_get(v_a_954_, 2);
        v_ref_962_ = crate::leanh::lean_ctor_get(v_a_954_, 5);
        v___x_963_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_964_ = l_Lean_Syntax_getArg(v_x_953_, v___x_963_);
        v___x_965_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_966_ = l_Lean_Syntax_getArg(v_x_953_, v___x_965_);
        crate::leanh::lean_dec(v_x_953_);
        v___x_967_ = 0;
        v___x_968_ = l_Lean_SourceInfo_fromRef(v_ref_962_, v___x_967_);
        v___x_969_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_970_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6);
        v___x_971_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9;
        crate::leanh::lean_inc(v_currMacroScope_961_);
        crate::leanh::lean_inc(v_quotContext_960_);
        v___x_972_ = l_Lean_addMacroScope(v_quotContext_960_, v___x_971_, v_currMacroScope_961_);
        v___x_973_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11;
        crate::leanh::lean_inc_n(v___x_968_, 2);
        v___x_974_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_974_, 0, v___x_968_);
        crate::leanh::lean_ctor_set(v___x_974_, 1, v___x_970_);
        crate::leanh::lean_ctor_set(v___x_974_, 2, v___x_972_);
        crate::leanh::lean_ctor_set(v___x_974_, 3, v___x_973_);
        v___x_975_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_976_ = l_Lean_Syntax_node2(v___x_968_, v___x_975_, v___x_964_, v___x_966_);
        v___x_977_ = l_Lean_Syntax_node2(v___x_968_, v___x_969_, v___x_974_, v___x_976_);
        v___x_978_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_978_, 0, v___x_977_);
        crate::leanh::lean_ctor_set(v___x_978_, 1, v_a_955_);
        return v___x_978_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___boxed(
    mut v_x_979_: *mut crate::leanh::LeanObject,
    mut v_a_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1(
        v_x_979_, v_a_980_, v_a_981_,
    );
    crate::leanh::lean_dec_ref(v_a_980_);
    return v_res_982_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(
    mut v_x_986_: *mut crate::leanh::LeanObject,
    mut v_a_987_: *mut crate::leanh::LeanObject,
    mut v_a_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    v___x_989_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    crate::leanh::lean_inc(v_x_986_);
    v___x_990_ = l_Lean_Syntax_isOfKind(v_x_986_, v___x_989_);
    if v___x_990_ == 0 {
        let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_986_);
        v___x_991_ = crate::leanh::lean_box(0);
        v___x_992_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_992_, 0, v___x_991_);
        crate::leanh::lean_ctor_set(v___x_992_, 1, v_a_988_);
        return v___x_992_;
    } else {
        let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_996_: u8 = 0;
        v___x_993_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_994_ = l_Lean_Syntax_getArg(v_x_986_, v___x_993_);
        v___x_995_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        crate::leanh::lean_inc(v___x_994_);
        v___x_996_ = l_Lean_Syntax_isOfKind(v___x_994_, v___x_995_);
        if v___x_996_ == 0 {
            let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_994_);
            crate::leanh::lean_dec(v_x_986_);
            v___x_997_ = crate::leanh::lean_box(0);
            v___x_998_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_998_, 0, v___x_997_);
            crate::leanh::lean_ctor_set(v___x_998_, 1, v_a_988_);
            return v___x_998_;
        } else {
            let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1002_: u8 = 0;
            v___x_999_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1000_ = l_Lean_Syntax_getArg(v_x_986_, v___x_999_);
            crate::leanh::lean_dec(v_x_986_);
            v___x_1001_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1000_);
            v___x_1002_ = l_Lean_Syntax_matchesNull(v___x_1000_, v___x_1001_);
            if v___x_1002_ == 0 {
                let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1000_);
                crate::leanh::lean_dec(v___x_994_);
                v___x_1003_ = crate::leanh::lean_box(0);
                v___x_1004_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1004_, 0, v___x_1003_);
                crate::leanh::lean_ctor_set(v___x_1004_, 1, v_a_988_);
                return v___x_1004_;
            } else {
                let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1008_: u8 = 0;
                let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1005_ = l_Lean_Syntax_getArg(v___x_1000_, v___x_993_);
                v___x_1006_ = l_Lean_Syntax_getArg(v___x_1000_, v___x_999_);
                crate::leanh::lean_dec(v___x_1000_);
                v_ref_1007_ = l_Lean_replaceRef(v___x_994_, v_a_987_);
                crate::leanh::lean_dec(v___x_994_);
                v___x_1008_ = 0;
                v___x_1009_ = l_Lean_SourceInfo_fromRef(v_ref_1007_, v___x_1008_);
                crate::leanh::lean_dec(v_ref_1007_);
                v___x_1010_ = l_term___x3c_x26_x3e___00__closed__1;
                v___x_1011_ = l_term___x3c_x26_x3e___00__closed__4;
                crate::leanh::lean_inc(v___x_1009_);
                v___x_1012_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1012_, 0, v___x_1009_);
                crate::leanh::lean_ctor_set(v___x_1012_, 1, v___x_1011_);
                v___x_1013_ = l_Lean_Syntax_node3(
                    v___x_1009_,
                    v___x_1010_,
                    v___x_1005_,
                    v___x_1012_,
                    v___x_1006_,
                );
                v___x_1014_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1014_, 0, v___x_1013_);
                crate::leanh::lean_ctor_set(v___x_1014_, 1, v_a_988_);
                return v___x_1014_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___boxed(
    mut v_x_1015_: *mut crate::leanh::LeanObject,
    mut v_a_1016_: *mut crate::leanh::LeanObject,
    mut v_a_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(
        v_x_1015_, v_a_1016_, v_a_1017_,
    );
    crate::leanh::lean_dec(v_a_1016_);
    return v_res_1018_;
}
pub unsafe fn l_Functor_discard___redArg(
    mut v_inst_1019_: *mut crate::leanh::LeanObject,
    mut v_x_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mapConst_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mapConst_1021_ = crate::leanh::lean_ctor_get(v_inst_1019_, 1);
    crate::leanh::lean_inc(v_mapConst_1021_);
    crate::leanh::lean_dec_ref(v_inst_1019_);
    v___x_1022_ = crate::leanh::lean_box(0);
    v___x_1023_ = crate::leanh::lean_apply_4(
        v_mapConst_1021_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1022_,
        v_x_1020_,
    );
    return v___x_1023_;
}
pub unsafe fn l_Functor_discard(
    mut v_f_1024_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1025_: *mut crate::leanh::LeanObject,
    mut v_inst_1026_: *mut crate::leanh::LeanObject,
    mut v_x_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mapConst_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mapConst_1028_ = crate::leanh::lean_ctor_get(v_inst_1026_, 1);
    crate::leanh::lean_inc(v_mapConst_1028_);
    crate::leanh::lean_dec_ref(v_inst_1026_);
    v___x_1029_ = crate::leanh::lean_box(0);
    v___x_1030_ = crate::leanh::lean_apply_4(
        v_mapConst_1028_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1029_,
        v_x_1027_,
    );
    return v___x_1030_;
}
pub unsafe fn l_instOrElseOfAlternative___redArg(
    mut v_inst_1031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_orElse_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1032_ = crate::leanh::lean_ctor_get(v_inst_1031_, 2);
    crate::leanh::lean_inc(v_orElse_1032_);
    crate::leanh::lean_dec_ref(v_inst_1031_);
    v___x_1033_ = crate::leanh::lean_apply_1(v_orElse_1032_, crate::leanh::lean_box(0));
    return v___x_1033_;
}
pub unsafe fn l_instOrElseOfAlternative(
    mut v_f_1034_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1035_: *mut crate::leanh::LeanObject,
    mut v_inst_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_instOrElseOfAlternative___redArg(v_inst_1036_);
    return v___x_1037_;
}
pub unsafe fn l_guard___redArg(
    mut v_inst_1038_: *mut crate::leanh::LeanObject,
    mut v_inst_1039_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_inst_1039_ == 0 {
        let mut v_failure_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_failure_1040_ = crate::leanh::lean_ctor_get(v_inst_1038_, 1);
        crate::leanh::lean_inc(v_failure_1040_);
        crate::leanh::lean_dec_ref(v_inst_1038_);
        v___x_1041_ = crate::leanh::lean_apply_1(v_failure_1040_, crate::leanh::lean_box(0));
        return v___x_1041_;
    } else {
        let mut v_toApplicative_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1042_ = crate::leanh::lean_ctor_get(v_inst_1038_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1042_);
        crate::leanh::lean_dec_ref(v_inst_1038_);
        v_toPure_1043_ = crate::leanh::lean_ctor_get(v_toApplicative_1042_, 1);
        crate::leanh::lean_inc(v_toPure_1043_);
        crate::leanh::lean_dec_ref(v_toApplicative_1042_);
        v___x_1044_ = crate::leanh::lean_box(0);
        v___x_1045_ =
            crate::leanh::lean_apply_2(v_toPure_1043_, crate::leanh::lean_box(0), v___x_1044_);
        return v___x_1045_;
    }
}
pub unsafe fn l_guard___redArg___boxed(
    mut v_inst_1046_: *mut crate::leanh::LeanObject,
    mut v_inst_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_22__boxed_1048_: u8 = 0;
    let mut v_res_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_22__boxed_1048_ = (crate::leanh::lean_unbox(v_inst_1047_) as u8);
    v_res_1049_ = l_guard___redArg(v_inst_1046_, v_inst_22__boxed_1048_);
    return v_res_1049_;
}
pub unsafe fn l_guard(
    mut v_f_1050_: *mut crate::leanh::LeanObject,
    mut v_inst_1051_: *mut crate::leanh::LeanObject,
    mut v_p_1052_: *mut crate::leanh::LeanObject,
    mut v_inst_1053_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_inst_1053_ == 0 {
        let mut v_failure_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_failure_1054_ = crate::leanh::lean_ctor_get(v_inst_1051_, 1);
        crate::leanh::lean_inc(v_failure_1054_);
        crate::leanh::lean_dec_ref(v_inst_1051_);
        v___x_1055_ = crate::leanh::lean_apply_1(v_failure_1054_, crate::leanh::lean_box(0));
        return v___x_1055_;
    } else {
        let mut v_toApplicative_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1056_ = crate::leanh::lean_ctor_get(v_inst_1051_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1056_);
        crate::leanh::lean_dec_ref(v_inst_1051_);
        v_toPure_1057_ = crate::leanh::lean_ctor_get(v_toApplicative_1056_, 1);
        crate::leanh::lean_inc(v_toPure_1057_);
        crate::leanh::lean_dec_ref(v_toApplicative_1056_);
        v___x_1058_ = crate::leanh::lean_box(0);
        v___x_1059_ =
            crate::leanh::lean_apply_2(v_toPure_1057_, crate::leanh::lean_box(0), v___x_1058_);
        return v___x_1059_;
    }
}
pub unsafe fn l_guard___boxed(
    mut v_f_1060_: *mut crate::leanh::LeanObject,
    mut v_inst_1061_: *mut crate::leanh::LeanObject,
    mut v_p_1062_: *mut crate::leanh::LeanObject,
    mut v_inst_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_34__boxed_1064_: u8 = 0;
    let mut v_res_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_34__boxed_1064_ = (crate::leanh::lean_unbox(v_inst_1063_) as u8);
    v_res_1065_ = l_guard(v_f_1060_, v_inst_1061_, v_p_1062_, v_inst_34__boxed_1064_);
    return v_res_1065_;
}
pub unsafe fn l_optional___redArg___lam__0(
    mut v_val_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1067_, 0, v_val_1066_);
    return v___x_1067_;
}
pub unsafe fn l_optional___redArg___lam__1(
    mut v_toPure_1068_: *mut crate::leanh::LeanObject,
    mut v_x_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = crate::leanh::lean_box(0);
    v___x_1071_ =
        crate::leanh::lean_apply_2(v_toPure_1068_, crate::leanh::lean_box(0), v___x_1070_);
    return v___x_1071_;
}
pub unsafe fn l_optional___redArg(
    mut v_inst_1073_: *mut crate::leanh::LeanObject,
    mut v_x_1074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_orElse_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1075_ = crate::leanh::lean_ctor_get(v_inst_1073_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1075_);
    v_toFunctor_1076_ = crate::leanh::lean_ctor_get(v_toApplicative_1075_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1076_);
    v_orElse_1077_ = crate::leanh::lean_ctor_get(v_inst_1073_, 2);
    crate::leanh::lean_inc(v_orElse_1077_);
    crate::leanh::lean_dec_ref(v_inst_1073_);
    v_toPure_1078_ = crate::leanh::lean_ctor_get(v_toApplicative_1075_, 1);
    crate::leanh::lean_inc(v_toPure_1078_);
    crate::leanh::lean_dec_ref(v_toApplicative_1075_);
    v_map_1079_ = crate::leanh::lean_ctor_get(v_toFunctor_1076_, 0);
    crate::leanh::lean_inc(v_map_1079_);
    crate::leanh::lean_dec_ref(v_toFunctor_1076_);
    v___f_1080_ = l_optional___redArg___closed__0;
    v___f_1081_ = crate::leanh::lean_alloc_closure(
        l_optional___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1081_, 0, v_toPure_1078_);
    v___x_1082_ = crate::leanh::lean_apply_4(
        v_map_1079_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1080_,
        v_x_1074_,
    );
    v___x_1083_ = crate::leanh::lean_apply_3(
        v_orElse_1077_,
        crate::leanh::lean_box(0),
        v___x_1082_,
        v___f_1081_,
    );
    return v___x_1083_;
}
pub unsafe fn l_optional(
    mut v_f_1084_: *mut crate::leanh::LeanObject,
    mut v_inst_1085_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1086_: *mut crate::leanh::LeanObject,
    mut v_x_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_orElse_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1088_ = crate::leanh::lean_ctor_get(v_inst_1085_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1088_);
    v_toFunctor_1089_ = crate::leanh::lean_ctor_get(v_toApplicative_1088_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_1089_);
    v_orElse_1090_ = crate::leanh::lean_ctor_get(v_inst_1085_, 2);
    crate::leanh::lean_inc(v_orElse_1090_);
    crate::leanh::lean_dec_ref(v_inst_1085_);
    v_toPure_1091_ = crate::leanh::lean_ctor_get(v_toApplicative_1088_, 1);
    crate::leanh::lean_inc(v_toPure_1091_);
    crate::leanh::lean_dec_ref(v_toApplicative_1088_);
    v_map_1092_ = crate::leanh::lean_ctor_get(v_toFunctor_1089_, 0);
    crate::leanh::lean_inc(v_map_1092_);
    crate::leanh::lean_dec_ref(v_toFunctor_1089_);
    v___f_1093_ = l_optional___redArg___closed__0;
    v___f_1094_ = crate::leanh::lean_alloc_closure(
        l_optional___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1094_, 0, v_toPure_1091_);
    v___x_1095_ = crate::leanh::lean_apply_4(
        v_map_1092_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1093_,
        v_x_1087_,
    );
    v___x_1096_ = crate::leanh::lean_apply_3(
        v_orElse_1090_,
        crate::leanh::lean_box(0),
        v___x_1095_,
        v___f_1094_,
    );
    return v___x_1096_;
}
pub unsafe fn l_instToBoolBool___lam__0(mut v_b_1097_: u8) -> u8 {
    return v_b_1097_;
}
pub unsafe fn l_instToBoolBool___lam__0___boxed(
    mut v_b_1098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1099_: u8 = 0;
    let mut v_res_1100_: u8 = 0;
    let mut v_r_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1099_ = (crate::leanh::lean_unbox(v_b_1098_) as u8);
    v_res_1100_ = l_instToBoolBool___lam__0(v_b_boxed_1099_);
    v_r_1101_ = crate::leanh::lean_box((v_res_1100_) as usize);
    return v_r_1101_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1124_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0;
    v___x_1125_ = l_String_toRawSubstring_x27(v___x_1124_);
    return v___x_1125_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(
    mut v_x_1134_: *mut crate::leanh::LeanObject,
    mut v_a_1135_: *mut crate::leanh::LeanObject,
    mut v_a_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: u8 = 0;
    v___x_1137_ = l_term___x3c_x7c_x7c_x3e___00__closed__1;
    crate::leanh::lean_inc(v_x_1134_);
    v___x_1138_ = l_Lean_Syntax_isOfKind(v_x_1134_, v___x_1137_);
    if v___x_1138_ == 0 {
        let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1134_);
        v___x_1139_ = crate::leanh::lean_box(1);
        v___x_1140_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1140_, 0, v___x_1139_);
        crate::leanh::lean_ctor_set(v___x_1140_, 1, v_a_1136_);
        return v___x_1140_;
    } else {
        let mut v_quotContext_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1148_: u8 = 0;
        let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1141_ = crate::leanh::lean_ctor_get(v_a_1135_, 1);
        v_currMacroScope_1142_ = crate::leanh::lean_ctor_get(v_a_1135_, 2);
        v_ref_1143_ = crate::leanh::lean_ctor_get(v_a_1135_, 5);
        v___x_1144_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1145_ = l_Lean_Syntax_getArg(v_x_1134_, v___x_1144_);
        v___x_1146_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1147_ = l_Lean_Syntax_getArg(v_x_1134_, v___x_1146_);
        crate::leanh::lean_dec(v_x_1134_);
        v___x_1148_ = 0;
        v___x_1149_ = l_Lean_SourceInfo_fromRef(v_ref_1143_, v___x_1148_);
        v___x_1150_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1151_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1);
        v___x_1152_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_1142_);
        crate::leanh::lean_inc(v_quotContext_1141_);
        v___x_1153_ =
            l_Lean_addMacroScope(v_quotContext_1141_, v___x_1152_, v_currMacroScope_1142_);
        v___x_1154_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4;
        crate::leanh::lean_inc_n(v___x_1149_, 2);
        v___x_1155_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1155_, 0, v___x_1149_);
        crate::leanh::lean_ctor_set(v___x_1155_, 1, v___x_1151_);
        crate::leanh::lean_ctor_set(v___x_1155_, 2, v___x_1153_);
        crate::leanh::lean_ctor_set(v___x_1155_, 3, v___x_1154_);
        v___x_1156_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1157_ = l_Lean_Syntax_node2(v___x_1149_, v___x_1156_, v___x_1145_, v___x_1147_);
        v___x_1158_ = l_Lean_Syntax_node2(v___x_1149_, v___x_1150_, v___x_1155_, v___x_1157_);
        v___x_1159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1159_, 0, v___x_1158_);
        crate::leanh::lean_ctor_set(v___x_1159_, 1, v_a_1136_);
        return v___x_1159_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___boxed(
    mut v_x_1160_: *mut crate::leanh::LeanObject,
    mut v_a_1161_: *mut crate::leanh::LeanObject,
    mut v_a_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1163_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(
        v_x_1160_, v_a_1161_, v_a_1162_,
    );
    crate::leanh::lean_dec_ref(v_a_1161_);
    return v_res_1163_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__orM__1(
    mut v_x_1164_: *mut crate::leanh::LeanObject,
    mut v_a_1165_: *mut crate::leanh::LeanObject,
    mut v_a_1166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u8 = 0;
    v___x_1167_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    crate::leanh::lean_inc(v_x_1164_);
    v___x_1168_ = l_Lean_Syntax_isOfKind(v_x_1164_, v___x_1167_);
    if v___x_1168_ == 0 {
        let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1164_);
        v___x_1169_ = crate::leanh::lean_box(0);
        v___x_1170_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1169_);
        crate::leanh::lean_ctor_set(v___x_1170_, 1, v_a_1166_);
        return v___x_1170_;
    } else {
        let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: u8 = 0;
        v___x_1171_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1172_ = l_Lean_Syntax_getArg(v_x_1164_, v___x_1171_);
        v___x_1173_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        crate::leanh::lean_inc(v___x_1172_);
        v___x_1174_ = l_Lean_Syntax_isOfKind(v___x_1172_, v___x_1173_);
        if v___x_1174_ == 0 {
            let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1172_);
            crate::leanh::lean_dec(v_x_1164_);
            v___x_1175_ = crate::leanh::lean_box(0);
            v___x_1176_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1176_, 0, v___x_1175_);
            crate::leanh::lean_ctor_set(v___x_1176_, 1, v_a_1166_);
            return v___x_1176_;
        } else {
            let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1180_: u8 = 0;
            v___x_1177_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1178_ = l_Lean_Syntax_getArg(v_x_1164_, v___x_1177_);
            crate::leanh::lean_dec(v_x_1164_);
            v___x_1179_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1178_);
            v___x_1180_ = l_Lean_Syntax_matchesNull(v___x_1178_, v___x_1179_);
            if v___x_1180_ == 0 {
                let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1178_);
                crate::leanh::lean_dec(v___x_1172_);
                v___x_1181_ = crate::leanh::lean_box(0);
                v___x_1182_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1182_, 0, v___x_1181_);
                crate::leanh::lean_ctor_set(v___x_1182_, 1, v_a_1166_);
                return v___x_1182_;
            } else {
                let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1186_: u8 = 0;
                let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1183_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_1171_);
                v___x_1184_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_1177_);
                crate::leanh::lean_dec(v___x_1178_);
                v_ref_1185_ = l_Lean_replaceRef(v___x_1172_, v_a_1165_);
                crate::leanh::lean_dec(v___x_1172_);
                v___x_1186_ = 0;
                v___x_1187_ = l_Lean_SourceInfo_fromRef(v_ref_1185_, v___x_1186_);
                crate::leanh::lean_dec(v_ref_1185_);
                v___x_1188_ = l_term___x3c_x7c_x7c_x3e___00__closed__1;
                v___x_1189_ = l_term___x3c_x7c_x7c_x3e___00__closed__2;
                crate::leanh::lean_inc(v___x_1187_);
                v___x_1190_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1190_, 0, v___x_1187_);
                crate::leanh::lean_ctor_set(v___x_1190_, 1, v___x_1189_);
                v___x_1191_ = l_Lean_Syntax_node3(
                    v___x_1187_,
                    v___x_1188_,
                    v___x_1183_,
                    v___x_1190_,
                    v___x_1184_,
                );
                v___x_1192_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1192_, 0, v___x_1191_);
                crate::leanh::lean_ctor_set(v___x_1192_, 1, v_a_1166_);
                return v___x_1192_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__orM__1___boxed(
    mut v_x_1193_: *mut crate::leanh::LeanObject,
    mut v_a_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ =
        l___aux__Init__Control__Basic______unexpand__orM__1(v_x_1193_, v_a_1194_, v_a_1195_);
    crate::leanh::lean_dec(v_a_1194_);
    return v_res_1196_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0;
    v___x_1218_ = l_String_toRawSubstring_x27(v___x_1217_);
    return v___x_1218_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(
    mut v_x_1227_: *mut crate::leanh::LeanObject,
    mut v_a_1228_: *mut crate::leanh::LeanObject,
    mut v_a_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: u8 = 0;
    v___x_1230_ = l_term___x3c_x26_x26_x3e___00__closed__1;
    crate::leanh::lean_inc(v_x_1227_);
    v___x_1231_ = l_Lean_Syntax_isOfKind(v_x_1227_, v___x_1230_);
    if v___x_1231_ == 0 {
        let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1227_);
        v___x_1232_ = crate::leanh::lean_box(1);
        v___x_1233_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1233_, 0, v___x_1232_);
        crate::leanh::lean_ctor_set(v___x_1233_, 1, v_a_1229_);
        return v___x_1233_;
    } else {
        let mut v_quotContext_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: u8 = 0;
        let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1234_ = crate::leanh::lean_ctor_get(v_a_1228_, 1);
        v_currMacroScope_1235_ = crate::leanh::lean_ctor_get(v_a_1228_, 2);
        v_ref_1236_ = crate::leanh::lean_ctor_get(v_a_1228_, 5);
        v___x_1237_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1238_ = l_Lean_Syntax_getArg(v_x_1227_, v___x_1237_);
        v___x_1239_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1240_ = l_Lean_Syntax_getArg(v_x_1227_, v___x_1239_);
        crate::leanh::lean_dec(v_x_1227_);
        v___x_1241_ = 0;
        v___x_1242_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1241_);
        v___x_1243_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1244_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1);
        v___x_1245_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_1235_);
        crate::leanh::lean_inc(v_quotContext_1234_);
        v___x_1246_ =
            l_Lean_addMacroScope(v_quotContext_1234_, v___x_1245_, v_currMacroScope_1235_);
        v___x_1247_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4;
        crate::leanh::lean_inc_n(v___x_1242_, 2);
        v___x_1248_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1248_, 0, v___x_1242_);
        crate::leanh::lean_ctor_set(v___x_1248_, 1, v___x_1244_);
        crate::leanh::lean_ctor_set(v___x_1248_, 2, v___x_1246_);
        crate::leanh::lean_ctor_set(v___x_1248_, 3, v___x_1247_);
        v___x_1249_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1250_ = l_Lean_Syntax_node2(v___x_1242_, v___x_1249_, v___x_1238_, v___x_1240_);
        v___x_1251_ = l_Lean_Syntax_node2(v___x_1242_, v___x_1243_, v___x_1248_, v___x_1250_);
        v___x_1252_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1252_, 0, v___x_1251_);
        crate::leanh::lean_ctor_set(v___x_1252_, 1, v_a_1229_);
        return v___x_1252_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___boxed(
    mut v_x_1253_: *mut crate::leanh::LeanObject,
    mut v_a_1254_: *mut crate::leanh::LeanObject,
    mut v_a_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1256_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(
        v_x_1253_, v_a_1254_, v_a_1255_,
    );
    crate::leanh::lean_dec_ref(v_a_1254_);
    return v_res_1256_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__andM__1(
    mut v_x_1257_: *mut crate::leanh::LeanObject,
    mut v_a_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: u8 = 0;
    v___x_1260_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    crate::leanh::lean_inc(v_x_1257_);
    v___x_1261_ = l_Lean_Syntax_isOfKind(v_x_1257_, v___x_1260_);
    if v___x_1261_ == 0 {
        let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1257_);
        v___x_1262_ = crate::leanh::lean_box(0);
        v___x_1263_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1263_, 0, v___x_1262_);
        crate::leanh::lean_ctor_set(v___x_1263_, 1, v_a_1259_);
        return v___x_1263_;
    } else {
        let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: u8 = 0;
        v___x_1264_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1265_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1264_);
        v___x_1266_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        crate::leanh::lean_inc(v___x_1265_);
        v___x_1267_ = l_Lean_Syntax_isOfKind(v___x_1265_, v___x_1266_);
        if v___x_1267_ == 0 {
            let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1265_);
            crate::leanh::lean_dec(v_x_1257_);
            v___x_1268_ = crate::leanh::lean_box(0);
            v___x_1269_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1269_, 0, v___x_1268_);
            crate::leanh::lean_ctor_set(v___x_1269_, 1, v_a_1259_);
            return v___x_1269_;
        } else {
            let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1273_: u8 = 0;
            v___x_1270_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1271_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1270_);
            crate::leanh::lean_dec(v_x_1257_);
            v___x_1272_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1271_);
            v___x_1273_ = l_Lean_Syntax_matchesNull(v___x_1271_, v___x_1272_);
            if v___x_1273_ == 0 {
                let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1271_);
                crate::leanh::lean_dec(v___x_1265_);
                v___x_1274_ = crate::leanh::lean_box(0);
                v___x_1275_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1275_, 0, v___x_1274_);
                crate::leanh::lean_ctor_set(v___x_1275_, 1, v_a_1259_);
                return v___x_1275_;
            } else {
                let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1279_: u8 = 0;
                let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1276_ = l_Lean_Syntax_getArg(v___x_1271_, v___x_1264_);
                v___x_1277_ = l_Lean_Syntax_getArg(v___x_1271_, v___x_1270_);
                crate::leanh::lean_dec(v___x_1271_);
                v_ref_1278_ = l_Lean_replaceRef(v___x_1265_, v_a_1258_);
                crate::leanh::lean_dec(v___x_1265_);
                v___x_1279_ = 0;
                v___x_1280_ = l_Lean_SourceInfo_fromRef(v_ref_1278_, v___x_1279_);
                crate::leanh::lean_dec(v_ref_1278_);
                v___x_1281_ = l_term___x3c_x26_x26_x3e___00__closed__1;
                v___x_1282_ = l_term___x3c_x26_x26_x3e___00__closed__2;
                crate::leanh::lean_inc(v___x_1280_);
                v___x_1283_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1283_, 0, v___x_1280_);
                crate::leanh::lean_ctor_set(v___x_1283_, 1, v___x_1282_);
                v___x_1284_ = l_Lean_Syntax_node3(
                    v___x_1280_,
                    v___x_1281_,
                    v___x_1276_,
                    v___x_1283_,
                    v___x_1277_,
                );
                v___x_1285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1285_, 0, v___x_1284_);
                crate::leanh::lean_ctor_set(v___x_1285_, 1, v_a_1259_);
                return v___x_1285_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__andM__1___boxed(
    mut v_x_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ =
        l___aux__Init__Control__Basic______unexpand__andM__1(v_x_1286_, v_a_1287_, v_a_1288_);
    crate::leanh::lean_dec(v_a_1287_);
    return v_res_1289_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__0(
    mut v_x_u2082_1290_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_1291_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ =
        crate::leanh::lean_apply_2(v_x_u2082_1290_, crate::leanh::lean_box(0), v___y_1293_);
    v___x_1295_ =
        crate::leanh::lean_apply_2(v_x_u2081_1291_, crate::leanh::lean_box(0), v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__1(
    mut v_x_u2082_1296_: *mut crate::leanh::LeanObject,
    mut v_f_1297_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1299_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1299_, 0, v_x_u2082_1296_);
    crate::leanh::lean_closure_set(v___f_1299_, 1, v_x_u2081_1298_);
    v___x_1300_ = crate::leanh::lean_apply_1(v_f_1297_, v___f_1299_);
    return v___x_1300_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__2(
    mut v_inst_1301_: *mut crate::leanh::LeanObject,
    mut v_f_1302_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_liftWith_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1304_ = crate::leanh::lean_ctor_get(v_inst_1301_, 0);
    crate::leanh::lean_inc(v_liftWith_1304_);
    crate::leanh::lean_dec_ref(v_inst_1301_);
    v___f_1305_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1305_, 0, v_x_u2082_1303_);
    crate::leanh::lean_closure_set(v___f_1305_, 1, v_f_1302_);
    v___x_1306_ =
        crate::leanh::lean_apply_2(v_liftWith_1304_, crate::leanh::lean_box(0), v___f_1305_);
    return v___x_1306_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__3(
    mut v_inst_1307_: *mut crate::leanh::LeanObject,
    mut v_inst_1308_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1309_: *mut crate::leanh::LeanObject,
    mut v_f_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_liftWith_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1311_ = crate::leanh::lean_ctor_get(v_inst_1307_, 0);
    crate::leanh::lean_inc(v_liftWith_1311_);
    crate::leanh::lean_dec_ref(v_inst_1307_);
    v___f_1312_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1312_, 0, v_inst_1308_);
    crate::leanh::lean_closure_set(v___f_1312_, 1, v_f_1310_);
    v___x_1313_ =
        crate::leanh::lean_apply_2(v_liftWith_1311_, crate::leanh::lean_box(0), v___f_1312_);
    return v___x_1313_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__4(
    mut v_inst_1314_: *mut crate::leanh::LeanObject,
    mut v_inst_1315_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_restoreM_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_restoreM_1318_ = crate::leanh::lean_ctor_get(v_inst_1314_, 1);
    crate::leanh::lean_inc(v_restoreM_1318_);
    crate::leanh::lean_dec_ref(v_inst_1314_);
    v_restoreM_1319_ = crate::leanh::lean_ctor_get(v_inst_1315_, 1);
    crate::leanh::lean_inc(v_restoreM_1319_);
    crate::leanh::lean_dec_ref(v_inst_1315_);
    v___x_1320_ =
        crate::leanh::lean_apply_2(v_restoreM_1319_, crate::leanh::lean_box(0), v___y_1317_);
    v___x_1321_ =
        crate::leanh::lean_apply_2(v_restoreM_1318_, crate::leanh::lean_box(0), v___x_1320_);
    return v___x_1321_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg(
    mut v_inst_1322_: *mut crate::leanh::LeanObject,
    mut v_inst_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1323_);
    crate::leanh::lean_inc_ref(v_inst_1322_);
    v___f_1324_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1324_, 0, v_inst_1322_);
    crate::leanh::lean_closure_set(v___f_1324_, 1, v_inst_1323_);
    v___f_1325_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1325_, 0, v_inst_1322_);
    crate::leanh::lean_closure_set(v___f_1325_, 1, v_inst_1323_);
    v___x_1326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1326_, 0, v___f_1324_);
    crate::leanh::lean_ctor_set(v___x_1326_, 1, v___f_1325_);
    return v___x_1326_;
}
pub unsafe fn l_instMonadControlTOfMonadControl(
    mut v_m_1327_: *mut crate::leanh::LeanObject,
    mut v_n_1328_: *mut crate::leanh::LeanObject,
    mut v_o_1329_: *mut crate::leanh::LeanObject,
    mut v_inst_1330_: *mut crate::leanh::LeanObject,
    mut v_inst_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1331_);
    crate::leanh::lean_inc_ref(v_inst_1330_);
    v___f_1332_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1332_, 0, v_inst_1330_);
    crate::leanh::lean_closure_set(v___f_1332_, 1, v_inst_1331_);
    v___f_1333_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1333_, 0, v_inst_1330_);
    crate::leanh::lean_closure_set(v___f_1333_, 1, v_inst_1331_);
    v___x_1334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1334_, 0, v___f_1332_);
    crate::leanh::lean_ctor_set(v___x_1334_, 1, v___f_1333_);
    return v___x_1334_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__0(
    mut v_00_u03b2_1335_: *mut crate::leanh::LeanObject,
    mut v_x_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1336_);
    return v_x_1336_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__0___boxed(
    mut v_00_u03b2_1337_: *mut crate::leanh::LeanObject,
    mut v_x_1338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1339_ = l_instMonadControlTOfPure___redArg___lam__0(v_00_u03b2_1337_, v_x_1338_);
    crate::leanh::lean_dec(v_x_1338_);
    return v_res_1339_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__1(
    mut v___f_1340_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1341_: *mut crate::leanh::LeanObject,
    mut v_f_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = crate::leanh::lean_apply_1(v_f_1342_, v___f_1340_);
    return v___x_1343_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__2(
    mut v_inst_1344_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1345_: *mut crate::leanh::LeanObject,
    mut v_x_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = crate::leanh::lean_apply_2(v_inst_1344_, crate::leanh::lean_box(0), v_x_1346_);
    return v___x_1347_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg(
    mut v_inst_1351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1352_ = l_instMonadControlTOfPure___redArg___closed__1;
    v___f_1353_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlTOfPure___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1353_, 0, v_inst_1351_);
    v___x_1354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1354_, 0, v___f_1352_);
    crate::leanh::lean_ctor_set(v___x_1354_, 1, v___f_1353_);
    return v___x_1354_;
}
pub unsafe fn l_instMonadControlTOfPure(
    mut v_m_1355_: *mut crate::leanh::LeanObject,
    mut v_inst_1356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_instMonadControlTOfPure___redArg(v_inst_1356_);
    return v___x_1357_;
}
pub unsafe fn l_controlAt___redArg(
    mut v_inst_1358_: *mut crate::leanh::LeanObject,
    mut v_inst_1359_: *mut crate::leanh::LeanObject,
    mut v_f_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_liftWith_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1361_ = crate::leanh::lean_ctor_get(v_inst_1358_, 0);
    crate::leanh::lean_inc(v_liftWith_1361_);
    v_restoreM_1362_ = crate::leanh::lean_ctor_get(v_inst_1358_, 1);
    crate::leanh::lean_inc(v_restoreM_1362_);
    crate::leanh::lean_dec_ref(v_inst_1358_);
    v___x_1363_ =
        crate::leanh::lean_apply_2(v_liftWith_1361_, crate::leanh::lean_box(0), v_f_1360_);
    v___x_1364_ = crate::leanh::lean_apply_1(v_restoreM_1362_, crate::leanh::lean_box(0));
    v___x_1365_ = crate::leanh::lean_apply_4(
        v_inst_1359_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1363_,
        v___x_1364_,
    );
    return v___x_1365_;
}
pub unsafe fn l_controlAt(
    mut v_m_1366_: *mut crate::leanh::LeanObject,
    mut v_n_1367_: *mut crate::leanh::LeanObject,
    mut v_inst_1368_: *mut crate::leanh::LeanObject,
    mut v_inst_1369_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1370_: *mut crate::leanh::LeanObject,
    mut v_f_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_liftWith_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1372_ = crate::leanh::lean_ctor_get(v_inst_1368_, 0);
    crate::leanh::lean_inc(v_liftWith_1372_);
    v_restoreM_1373_ = crate::leanh::lean_ctor_get(v_inst_1368_, 1);
    crate::leanh::lean_inc(v_restoreM_1373_);
    crate::leanh::lean_dec_ref(v_inst_1368_);
    v___x_1374_ =
        crate::leanh::lean_apply_2(v_liftWith_1372_, crate::leanh::lean_box(0), v_f_1371_);
    v___x_1375_ = crate::leanh::lean_apply_1(v_restoreM_1373_, crate::leanh::lean_box(0));
    v___x_1376_ = crate::leanh::lean_apply_4(
        v_inst_1369_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1374_,
        v___x_1375_,
    );
    return v___x_1376_;
}
pub unsafe fn l_control___redArg(
    mut v_inst_1377_: *mut crate::leanh::LeanObject,
    mut v_inst_1378_: *mut crate::leanh::LeanObject,
    mut v_f_1379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_liftWith_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1380_ = crate::leanh::lean_ctor_get(v_inst_1377_, 0);
    crate::leanh::lean_inc(v_liftWith_1380_);
    v_restoreM_1381_ = crate::leanh::lean_ctor_get(v_inst_1377_, 1);
    crate::leanh::lean_inc(v_restoreM_1381_);
    crate::leanh::lean_dec_ref(v_inst_1377_);
    v___x_1382_ =
        crate::leanh::lean_apply_2(v_liftWith_1380_, crate::leanh::lean_box(0), v_f_1379_);
    v___x_1383_ = crate::leanh::lean_apply_1(v_restoreM_1381_, crate::leanh::lean_box(0));
    v___x_1384_ = crate::leanh::lean_apply_4(
        v_inst_1378_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1382_,
        v___x_1383_,
    );
    return v___x_1384_;
}
pub unsafe fn l_control(
    mut v_m_1385_: *mut crate::leanh::LeanObject,
    mut v_n_1386_: *mut crate::leanh::LeanObject,
    mut v_inst_1387_: *mut crate::leanh::LeanObject,
    mut v_inst_1388_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1389_: *mut crate::leanh::LeanObject,
    mut v_f_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_liftWith_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1391_ = crate::leanh::lean_ctor_get(v_inst_1387_, 0);
    crate::leanh::lean_inc(v_liftWith_1391_);
    v_restoreM_1392_ = crate::leanh::lean_ctor_get(v_inst_1387_, 1);
    crate::leanh::lean_inc(v_restoreM_1392_);
    crate::leanh::lean_dec_ref(v_inst_1387_);
    v___x_1393_ =
        crate::leanh::lean_apply_2(v_liftWith_1391_, crate::leanh::lean_box(0), v_f_1390_);
    v___x_1394_ = crate::leanh::lean_apply_1(v_restoreM_1392_, crate::leanh::lean_box(0));
    v___x_1395_ = crate::leanh::lean_apply_4(
        v_inst_1388_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1393_,
        v___x_1394_,
    );
    return v___x_1395_;
}
pub unsafe fn l_Bind_kleisliRight___redArg(
    mut v_inst_1396_: *mut crate::leanh::LeanObject,
    mut v_f_u2081_1397_: *mut crate::leanh::LeanObject,
    mut v_f_u2082_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = crate::leanh::lean_apply_1(v_f_u2081_1397_, v_a_1399_);
    v___x_1401_ = crate::leanh::lean_apply_4(
        v_inst_1396_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1400_,
        v_f_u2082_1398_,
    );
    return v___x_1401_;
}
pub unsafe fn l_Bind_kleisliRight(
    mut v_00_u03b1_1402_: *mut crate::leanh::LeanObject,
    mut v_m_1403_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1404_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1405_: *mut crate::leanh::LeanObject,
    mut v_inst_1406_: *mut crate::leanh::LeanObject,
    mut v_f_u2081_1407_: *mut crate::leanh::LeanObject,
    mut v_f_u2082_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = crate::leanh::lean_apply_1(v_f_u2081_1407_, v_a_1409_);
    v___x_1411_ = crate::leanh::lean_apply_4(
        v_inst_1406_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1410_,
        v_f_u2082_1408_,
    );
    return v___x_1411_;
}
pub unsafe fn l_Bind_kleisliLeft___redArg(
    mut v_inst_1412_: *mut crate::leanh::LeanObject,
    mut v_f_u2082_1413_: *mut crate::leanh::LeanObject,
    mut v_f_u2081_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = crate::leanh::lean_apply_1(v_f_u2081_1414_, v_a_1415_);
    v___x_1417_ = crate::leanh::lean_apply_4(
        v_inst_1412_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1416_,
        v_f_u2082_1413_,
    );
    return v___x_1417_;
}
pub unsafe fn l_Bind_kleisliLeft(
    mut v_00_u03b1_1418_: *mut crate::leanh::LeanObject,
    mut v_m_1419_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1420_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1421_: *mut crate::leanh::LeanObject,
    mut v_inst_1422_: *mut crate::leanh::LeanObject,
    mut v_f_u2082_1423_: *mut crate::leanh::LeanObject,
    mut v_f_u2081_1424_: *mut crate::leanh::LeanObject,
    mut v_a_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = crate::leanh::lean_apply_1(v_f_u2081_1424_, v_a_1425_);
    v___x_1427_ = crate::leanh::lean_apply_4(
        v_inst_1422_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1426_,
        v_f_u2082_1423_,
    );
    return v___x_1427_;
}
pub unsafe fn l_Bind_bindLeft___redArg(
    mut v_inst_1428_: *mut crate::leanh::LeanObject,
    mut v_f_1429_: *mut crate::leanh::LeanObject,
    mut v_ma_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = crate::leanh::lean_apply_4(
        v_inst_1428_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_ma_1430_,
        v_f_1429_,
    );
    return v___x_1431_;
}
pub unsafe fn l_Bind_bindLeft(
    mut v_00_u03b1_1432_: *mut crate::leanh::LeanObject,
    mut v_m_1433_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1434_: *mut crate::leanh::LeanObject,
    mut v_inst_1435_: *mut crate::leanh::LeanObject,
    mut v_f_1436_: *mut crate::leanh::LeanObject,
    mut v_ma_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = crate::leanh::lean_apply_4(
        v_inst_1435_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_ma_1437_,
        v_f_1436_,
    );
    return v___x_1438_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ =
        l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0;
    v___x_1460_ = l_String_toRawSubstring_x27(v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(
    mut v_x_1472_: *mut crate::leanh::LeanObject,
    mut v_a_1473_: *mut crate::leanh::LeanObject,
    mut v_a_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    v___x_1475_ = l_term___x3e_x3d_x3e___00__closed__1;
    crate::leanh::lean_inc(v_x_1472_);
    v___x_1476_ = l_Lean_Syntax_isOfKind(v_x_1472_, v___x_1475_);
    if v___x_1476_ == 0 {
        let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1472_);
        v___x_1477_ = crate::leanh::lean_box(1);
        v___x_1478_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1478_, 0, v___x_1477_);
        crate::leanh::lean_ctor_set(v___x_1478_, 1, v_a_1474_);
        return v___x_1478_;
    } else {
        let mut v_quotContext_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1486_: u8 = 0;
        let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1479_ = crate::leanh::lean_ctor_get(v_a_1473_, 1);
        v_currMacroScope_1480_ = crate::leanh::lean_ctor_get(v_a_1473_, 2);
        v_ref_1481_ = crate::leanh::lean_ctor_get(v_a_1473_, 5);
        v___x_1482_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1483_ = l_Lean_Syntax_getArg(v_x_1472_, v___x_1482_);
        v___x_1484_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1485_ = l_Lean_Syntax_getArg(v_x_1472_, v___x_1484_);
        crate::leanh::lean_dec(v_x_1472_);
        v___x_1486_ = 0;
        v___x_1487_ = l_Lean_SourceInfo_fromRef(v_ref_1481_, v___x_1486_);
        v___x_1488_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1489_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1);
        v___x_1490_ =
            l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4;
        crate::leanh::lean_inc(v_currMacroScope_1480_);
        crate::leanh::lean_inc(v_quotContext_1479_);
        v___x_1491_ =
            l_Lean_addMacroScope(v_quotContext_1479_, v___x_1490_, v_currMacroScope_1480_);
        v___x_1492_ =
            l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6;
        crate::leanh::lean_inc_n(v___x_1487_, 2);
        v___x_1493_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1493_, 0, v___x_1487_);
        crate::leanh::lean_ctor_set(v___x_1493_, 1, v___x_1489_);
        crate::leanh::lean_ctor_set(v___x_1493_, 2, v___x_1491_);
        crate::leanh::lean_ctor_set(v___x_1493_, 3, v___x_1492_);
        v___x_1494_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1495_ = l_Lean_Syntax_node2(v___x_1487_, v___x_1494_, v___x_1483_, v___x_1485_);
        v___x_1496_ = l_Lean_Syntax_node2(v___x_1487_, v___x_1488_, v___x_1493_, v___x_1495_);
        v___x_1497_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1497_, 0, v___x_1496_);
        crate::leanh::lean_ctor_set(v___x_1497_, 1, v_a_1474_);
        return v___x_1497_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___boxed(
    mut v_x_1498_: *mut crate::leanh::LeanObject,
    mut v_a_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(
        v_x_1498_, v_a_1499_, v_a_1500_,
    );
    crate::leanh::lean_dec_ref(v_a_1499_);
    return v_res_1501_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(
    mut v_x_1502_: *mut crate::leanh::LeanObject,
    mut v_a_1503_: *mut crate::leanh::LeanObject,
    mut v_a_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    v___x_1505_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    crate::leanh::lean_inc(v_x_1502_);
    v___x_1506_ = l_Lean_Syntax_isOfKind(v_x_1502_, v___x_1505_);
    if v___x_1506_ == 0 {
        let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1502_);
        v___x_1507_ = crate::leanh::lean_box(0);
        v___x_1508_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1508_, 0, v___x_1507_);
        crate::leanh::lean_ctor_set(v___x_1508_, 1, v_a_1504_);
        return v___x_1508_;
    } else {
        let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1512_: u8 = 0;
        v___x_1509_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1510_ = l_Lean_Syntax_getArg(v_x_1502_, v___x_1509_);
        v___x_1511_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        crate::leanh::lean_inc(v___x_1510_);
        v___x_1512_ = l_Lean_Syntax_isOfKind(v___x_1510_, v___x_1511_);
        if v___x_1512_ == 0 {
            let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1510_);
            crate::leanh::lean_dec(v_x_1502_);
            v___x_1513_ = crate::leanh::lean_box(0);
            v___x_1514_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1514_, 0, v___x_1513_);
            crate::leanh::lean_ctor_set(v___x_1514_, 1, v_a_1504_);
            return v___x_1514_;
        } else {
            let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1518_: u8 = 0;
            v___x_1515_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1516_ = l_Lean_Syntax_getArg(v_x_1502_, v___x_1515_);
            crate::leanh::lean_dec(v_x_1502_);
            v___x_1517_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1516_);
            v___x_1518_ = l_Lean_Syntax_matchesNull(v___x_1516_, v___x_1517_);
            if v___x_1518_ == 0 {
                let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1516_);
                crate::leanh::lean_dec(v___x_1510_);
                v___x_1519_ = crate::leanh::lean_box(0);
                v___x_1520_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                crate::leanh::lean_ctor_set(v___x_1520_, 1, v_a_1504_);
                return v___x_1520_;
            } else {
                let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1524_: u8 = 0;
                let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1521_ = l_Lean_Syntax_getArg(v___x_1516_, v___x_1509_);
                v___x_1522_ = l_Lean_Syntax_getArg(v___x_1516_, v___x_1515_);
                crate::leanh::lean_dec(v___x_1516_);
                v_ref_1523_ = l_Lean_replaceRef(v___x_1510_, v_a_1503_);
                crate::leanh::lean_dec(v___x_1510_);
                v___x_1524_ = 0;
                v___x_1525_ = l_Lean_SourceInfo_fromRef(v_ref_1523_, v___x_1524_);
                crate::leanh::lean_dec(v_ref_1523_);
                v___x_1526_ = l_term___x3e_x3d_x3e___00__closed__1;
                v___x_1527_ = l_term___x3e_x3d_x3e___00__closed__2;
                crate::leanh::lean_inc(v___x_1525_);
                v___x_1528_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1525_);
                crate::leanh::lean_ctor_set(v___x_1528_, 1, v___x_1527_);
                v___x_1529_ = l_Lean_Syntax_node3(
                    v___x_1525_,
                    v___x_1526_,
                    v___x_1521_,
                    v___x_1528_,
                    v___x_1522_,
                );
                v___x_1530_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1530_, 0, v___x_1529_);
                crate::leanh::lean_ctor_set(v___x_1530_, 1, v_a_1504_);
                return v___x_1530_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1___boxed(
    mut v_x_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(
        v_x_1531_, v_a_1532_, v_a_1533_,
    );
    crate::leanh::lean_dec(v_a_1532_);
    return v_res_1534_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0;
    v___x_1553_ = l_String_toRawSubstring_x27(v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(
    mut v_x_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    v___x_1567_ = l_term___x3c_x3d_x3c___00__closed__1;
    crate::leanh::lean_inc(v_x_1564_);
    v___x_1568_ = l_Lean_Syntax_isOfKind(v_x_1564_, v___x_1567_);
    if v___x_1568_ == 0 {
        let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1564_);
        v___x_1569_ = crate::leanh::lean_box(1);
        v___x_1570_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1570_, 0, v___x_1569_);
        crate::leanh::lean_ctor_set(v___x_1570_, 1, v_a_1566_);
        return v___x_1570_;
    } else {
        let mut v_quotContext_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: u8 = 0;
        let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1571_ = crate::leanh::lean_ctor_get(v_a_1565_, 1);
        v_currMacroScope_1572_ = crate::leanh::lean_ctor_get(v_a_1565_, 2);
        v_ref_1573_ = crate::leanh::lean_ctor_get(v_a_1565_, 5);
        v___x_1574_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1575_ = l_Lean_Syntax_getArg(v_x_1564_, v___x_1574_);
        v___x_1576_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1577_ = l_Lean_Syntax_getArg(v_x_1564_, v___x_1576_);
        crate::leanh::lean_dec(v_x_1564_);
        v___x_1578_ = 0;
        v___x_1579_ = l_Lean_SourceInfo_fromRef(v_ref_1573_, v___x_1578_);
        v___x_1580_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1581_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1);
        v___x_1582_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_1572_);
        crate::leanh::lean_inc(v_quotContext_1571_);
        v___x_1583_ =
            l_Lean_addMacroScope(v_quotContext_1571_, v___x_1582_, v_currMacroScope_1572_);
        v___x_1584_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5;
        crate::leanh::lean_inc_n(v___x_1579_, 2);
        v___x_1585_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1585_, 0, v___x_1579_);
        crate::leanh::lean_ctor_set(v___x_1585_, 1, v___x_1581_);
        crate::leanh::lean_ctor_set(v___x_1585_, 2, v___x_1583_);
        crate::leanh::lean_ctor_set(v___x_1585_, 3, v___x_1584_);
        v___x_1586_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1587_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1586_, v___x_1575_, v___x_1577_);
        v___x_1588_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1580_, v___x_1585_, v___x_1587_);
        v___x_1589_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1589_, 0, v___x_1588_);
        crate::leanh::lean_ctor_set(v___x_1589_, 1, v_a_1566_);
        return v___x_1589_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___boxed(
    mut v_x_1590_: *mut crate::leanh::LeanObject,
    mut v_a_1591_: *mut crate::leanh::LeanObject,
    mut v_a_1592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1593_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(
        v_x_1590_, v_a_1591_, v_a_1592_,
    );
    crate::leanh::lean_dec_ref(v_a_1591_);
    return v_res_1593_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(
    mut v_x_1594_: *mut crate::leanh::LeanObject,
    mut v_a_1595_: *mut crate::leanh::LeanObject,
    mut v_a_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: u8 = 0;
    v___x_1597_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    crate::leanh::lean_inc(v_x_1594_);
    v___x_1598_ = l_Lean_Syntax_isOfKind(v_x_1594_, v___x_1597_);
    if v___x_1598_ == 0 {
        let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1594_);
        v___x_1599_ = crate::leanh::lean_box(0);
        v___x_1600_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1600_, 0, v___x_1599_);
        crate::leanh::lean_ctor_set(v___x_1600_, 1, v_a_1596_);
        return v___x_1600_;
    } else {
        let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: u8 = 0;
        v___x_1601_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1602_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1601_);
        v___x_1603_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        crate::leanh::lean_inc(v___x_1602_);
        v___x_1604_ = l_Lean_Syntax_isOfKind(v___x_1602_, v___x_1603_);
        if v___x_1604_ == 0 {
            let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1602_);
            crate::leanh::lean_dec(v_x_1594_);
            v___x_1605_ = crate::leanh::lean_box(0);
            v___x_1606_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1606_, 0, v___x_1605_);
            crate::leanh::lean_ctor_set(v___x_1606_, 1, v_a_1596_);
            return v___x_1606_;
        } else {
            let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1610_: u8 = 0;
            v___x_1607_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1608_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1607_);
            crate::leanh::lean_dec(v_x_1594_);
            v___x_1609_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1608_);
            v___x_1610_ = l_Lean_Syntax_matchesNull(v___x_1608_, v___x_1609_);
            if v___x_1610_ == 0 {
                let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1608_);
                crate::leanh::lean_dec(v___x_1602_);
                v___x_1611_ = crate::leanh::lean_box(0);
                v___x_1612_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1612_, 0, v___x_1611_);
                crate::leanh::lean_ctor_set(v___x_1612_, 1, v_a_1596_);
                return v___x_1612_;
            } else {
                let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1616_: u8 = 0;
                let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1613_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1601_);
                v___x_1614_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1607_);
                crate::leanh::lean_dec(v___x_1608_);
                v_ref_1615_ = l_Lean_replaceRef(v___x_1602_, v_a_1595_);
                crate::leanh::lean_dec(v___x_1602_);
                v___x_1616_ = 0;
                v___x_1617_ = l_Lean_SourceInfo_fromRef(v_ref_1615_, v___x_1616_);
                crate::leanh::lean_dec(v_ref_1615_);
                v___x_1618_ = l_term___x3c_x3d_x3c___00__closed__1;
                v___x_1619_ = l_term___x3c_x3d_x3c___00__closed__2;
                crate::leanh::lean_inc(v___x_1617_);
                v___x_1620_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1620_, 0, v___x_1617_);
                crate::leanh::lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                v___x_1621_ = l_Lean_Syntax_node3(
                    v___x_1617_,
                    v___x_1618_,
                    v___x_1613_,
                    v___x_1620_,
                    v___x_1614_,
                );
                v___x_1622_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1622_, 0, v___x_1621_);
                crate::leanh::lean_ctor_set(v___x_1622_, 1, v_a_1596_);
                return v___x_1622_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1___boxed(
    mut v_x_1623_: *mut crate::leanh::LeanObject,
    mut v_a_1624_: *mut crate::leanh::LeanObject,
    mut v_a_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(
        v_x_1623_, v_a_1624_, v_a_1625_,
    );
    crate::leanh::lean_dec(v_a_1624_);
    return v_res_1626_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ =
        l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0;
    v___x_1645_ = l_String_toRawSubstring_x27(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(
    mut v_x_1656_: *mut crate::leanh::LeanObject,
    mut v_a_1657_: *mut crate::leanh::LeanObject,
    mut v_a_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    v___x_1659_ = l_term___x3d_x3c_x3c___00__closed__1;
    crate::leanh::lean_inc(v_x_1656_);
    v___x_1660_ = l_Lean_Syntax_isOfKind(v_x_1656_, v___x_1659_);
    if v___x_1660_ == 0 {
        let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1656_);
        v___x_1661_ = crate::leanh::lean_box(1);
        v___x_1662_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
        crate::leanh::lean_ctor_set(v___x_1662_, 1, v_a_1658_);
        return v___x_1662_;
    } else {
        let mut v_quotContext_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1670_: u8 = 0;
        let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1663_ = crate::leanh::lean_ctor_get(v_a_1657_, 1);
        v_currMacroScope_1664_ = crate::leanh::lean_ctor_get(v_a_1657_, 2);
        v_ref_1665_ = crate::leanh::lean_ctor_get(v_a_1657_, 5);
        v___x_1666_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1667_ = l_Lean_Syntax_getArg(v_x_1656_, v___x_1666_);
        v___x_1668_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1669_ = l_Lean_Syntax_getArg(v_x_1656_, v___x_1668_);
        crate::leanh::lean_dec(v_x_1656_);
        v___x_1670_ = 0;
        v___x_1671_ = l_Lean_SourceInfo_fromRef(v_ref_1665_, v___x_1670_);
        v___x_1672_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1673_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1);
        v___x_1674_ =
            l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_1664_);
        crate::leanh::lean_inc(v_quotContext_1663_);
        v___x_1675_ =
            l_Lean_addMacroScope(v_quotContext_1663_, v___x_1674_, v_currMacroScope_1664_);
        v___x_1676_ =
            l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5;
        crate::leanh::lean_inc_n(v___x_1671_, 2);
        v___x_1677_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1677_, 0, v___x_1671_);
        crate::leanh::lean_ctor_set(v___x_1677_, 1, v___x_1673_);
        crate::leanh::lean_ctor_set(v___x_1677_, 2, v___x_1675_);
        crate::leanh::lean_ctor_set(v___x_1677_, 3, v___x_1676_);
        v___x_1678_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1679_ = l_Lean_Syntax_node2(v___x_1671_, v___x_1678_, v___x_1667_, v___x_1669_);
        v___x_1680_ = l_Lean_Syntax_node2(v___x_1671_, v___x_1672_, v___x_1677_, v___x_1679_);
        v___x_1681_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1680_);
        crate::leanh::lean_ctor_set(v___x_1681_, 1, v_a_1658_);
        return v___x_1681_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___boxed(
    mut v_x_1682_: *mut crate::leanh::LeanObject,
    mut v_a_1683_: *mut crate::leanh::LeanObject,
    mut v_a_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1685_ = l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(
        v_x_1682_, v_a_1683_, v_a_1684_,
    );
    crate::leanh::lean_dec_ref(v_a_1683_);
    return v_res_1685_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(
    mut v_x_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    v___x_1689_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    crate::leanh::lean_inc(v_x_1686_);
    v___x_1690_ = l_Lean_Syntax_isOfKind(v_x_1686_, v___x_1689_);
    if v___x_1690_ == 0 {
        let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1686_);
        v___x_1691_ = crate::leanh::lean_box(0);
        v___x_1692_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1692_, 0, v___x_1691_);
        crate::leanh::lean_ctor_set(v___x_1692_, 1, v_a_1688_);
        return v___x_1692_;
    } else {
        let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1696_: u8 = 0;
        v___x_1693_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1694_ = l_Lean_Syntax_getArg(v_x_1686_, v___x_1693_);
        v___x_1695_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        crate::leanh::lean_inc(v___x_1694_);
        v___x_1696_ = l_Lean_Syntax_isOfKind(v___x_1694_, v___x_1695_);
        if v___x_1696_ == 0 {
            let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1694_);
            crate::leanh::lean_dec(v_x_1686_);
            v___x_1697_ = crate::leanh::lean_box(0);
            v___x_1698_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1698_, 0, v___x_1697_);
            crate::leanh::lean_ctor_set(v___x_1698_, 1, v_a_1688_);
            return v___x_1698_;
        } else {
            let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1702_: u8 = 0;
            v___x_1699_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1700_ = l_Lean_Syntax_getArg(v_x_1686_, v___x_1699_);
            crate::leanh::lean_dec(v_x_1686_);
            v___x_1701_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_1700_);
            v___x_1702_ = l_Lean_Syntax_matchesNull(v___x_1700_, v___x_1701_);
            if v___x_1702_ == 0 {
                let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1700_);
                crate::leanh::lean_dec(v___x_1694_);
                v___x_1703_ = crate::leanh::lean_box(0);
                v___x_1704_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1704_, 0, v___x_1703_);
                crate::leanh::lean_ctor_set(v___x_1704_, 1, v_a_1688_);
                return v___x_1704_;
            } else {
                let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1708_: u8 = 0;
                let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1705_ = l_Lean_Syntax_getArg(v___x_1700_, v___x_1693_);
                v___x_1706_ = l_Lean_Syntax_getArg(v___x_1700_, v___x_1699_);
                crate::leanh::lean_dec(v___x_1700_);
                v_ref_1707_ = l_Lean_replaceRef(v___x_1694_, v_a_1687_);
                crate::leanh::lean_dec(v___x_1694_);
                v___x_1708_ = 0;
                v___x_1709_ = l_Lean_SourceInfo_fromRef(v_ref_1707_, v___x_1708_);
                crate::leanh::lean_dec(v_ref_1707_);
                v___x_1710_ = l_term___x3d_x3c_x3c___00__closed__1;
                v___x_1711_ = l_term___x3d_x3c_x3c___00__closed__2;
                crate::leanh::lean_inc(v___x_1709_);
                v___x_1712_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1712_, 0, v___x_1709_);
                crate::leanh::lean_ctor_set(v___x_1712_, 1, v___x_1711_);
                v___x_1713_ = l_Lean_Syntax_node3(
                    v___x_1709_,
                    v___x_1710_,
                    v___x_1705_,
                    v___x_1712_,
                    v___x_1706_,
                );
                v___x_1714_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1714_, 0, v___x_1713_);
                crate::leanh::lean_ctor_set(v___x_1714_, 1, v_a_1688_);
                return v___x_1714_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1___boxed(
    mut v_x_1715_: *mut crate::leanh::LeanObject,
    mut v_a_1716_: *mut crate::leanh::LeanObject,
    mut v_a_1717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1718_ = l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(
        v_x_1715_, v_a_1716_, v_a_1717_,
    );
    crate::leanh::lean_dec(v_a_1716_);
    return v_res_1718_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Init_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_Basic(builtin);
}
