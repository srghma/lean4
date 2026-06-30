// Lean compiler output
// Module: Init.Control.Basic
// Imports: Init.Core Init.BinderNameHint
use crate::r#gen::Init::BinderNameHint::{
    initialize_Init_BinderNameHint, runtime_initialize_Init_BinderNameHint,
};
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
pub static l_term___x3c_x26_x3e___00__closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 60, 38, 62, 95, 0],
    };
static mut l_term___x3c_x26_x3e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__0_value)
                as *mut leanh::LeanObject,
            17902794450874024165 as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__2_value: leanh::LeanStringObject<8> =
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
static mut l_term___x3c_x26_x3e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__2_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__4_value: leanh::LeanStringObject<6> =
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
        m_data: [32, 60, 38, 62, 32, 0],
    };
static mut l_term___x3c_x26_x3e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__6_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_term___x3c_x26_x3e___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__6_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
                as *mut leanh::LeanObject,
            (((100 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__10_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((100 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((101 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x3e___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static mut l_term___x3c_x26_x3e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value
) as *mut leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [70, 117, 110, 99, 116, 111, 114, 46, 109, 97, 112, 82, 101, 118, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [70, 117, 110, 99, 116, 111, 114, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 97, 112, 82, 101, 118, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value
) as *mut leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value) as *mut leanh::LeanObject,2226500928782199335 as *mut leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value) as *mut leanh::LeanObject,17798854418672644188 as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value
        ) as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_optional___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_optional___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_optional___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_optional___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_instToBoolBool___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToBoolBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToBoolBool___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instToBoolBool___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instToBoolBool: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instToBoolBool___closed__0_value) as *mut leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 124, 124, 62, 95, 0],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__0_value)
                as *mut leanh::LeanObject,
            18177464721573610742 as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [32, 60, 124, 124, 62, 32, 0],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
                as *mut leanh::LeanObject,
            (((30 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__6_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((30 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((31 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_term___x3c_x7c_x7c_x3e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 114, 77, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value) as *mut leanh::LeanObject,17806001628258047394 as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 38, 38, 62, 95, 0],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__0_value)
                as *mut leanh::LeanObject,
            3935687535564439542 as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [32, 60, 38, 38, 62, 32, 0],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
                as *mut leanh::LeanObject,
            (((35 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__6_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((35 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((36 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_term___x3c_x26_x26_x3e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 110, 100, 77, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value) as *mut leanh::LeanObject,8873471052530828183 as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_instMonadControlTOfPure___redArg___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadControlTOfPure___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadControlTOfPure___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlTOfPure___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instMonadControlTOfPure___redArg___closed__1_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadControlTOfPure___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_instMonadControlTOfPure___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_instMonadControlTOfPure___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlTOfPure___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 62, 61, 62, 95, 0],
    };
static mut l_term___x3e_x3d_x3e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__0_value)
                as *mut leanh::LeanObject,
            376317980966388524 as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [32, 62, 61, 62, 32, 0],
    };
static mut l_term___x3e_x3d_x3e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value)
                as *mut leanh::LeanObject,
            (((55 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__6_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((55 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((56 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3e_x3d_x3e___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_term___x3e_x3d_x3e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [66, 105, 110, 100, 46, 107, 108, 101, 105, 115, 108, 105, 82, 105, 103, 104, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 105, 110, 100, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [107, 108, 101, 105, 115, 108, 105, 82, 105, 103, 104, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value
) as *mut leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,15820500991164727518 as *mut leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value) as *mut leanh::LeanObject,13518541916787333104 as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6_value
) as *mut leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 60, 61, 60, 95, 0],
    };
static mut l_term___x3c_x3d_x3c___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__0_value)
                as *mut leanh::LeanObject,
            6578201212627747956 as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x3d_x3c___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [32, 60, 61, 60, 32, 0],
    };
static mut l_term___x3c_x3d_x3c___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x3d_x3c___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x3d_x3c___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((55 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((56 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3c_x3d_x3c___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_term___x3c_x3d_x3c__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [66, 105, 110, 100, 46, 107, 108, 101, 105, 115, 108, 105, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [107, 108, 101, 105, 115, 108, 105, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value
) as *mut leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,15820500991164727518 as *mut leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value) as *mut leanh::LeanObject,2391163329140571260 as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5_value
) as *mut leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 61, 60, 60, 95, 0],
    };
static mut l_term___x3d_x3c_x3c___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__0_value)
                as *mut leanh::LeanObject,
            6202646376755925288 as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3d_x3c_x3c___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [32, 61, 60, 60, 32, 0],
    };
static mut l_term___x3d_x3c_x3c___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3d_x3c_x3c___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3d_x3c_x3c___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((55 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((56 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term___x3d_x3c_x3c___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_term___x3d_x3c_x3c__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [66, 105, 110, 100, 46, 98, 105, 110, 100, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 105, 110, 100, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value
) as *mut leanh::LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,15820500991164727518 as *mut leanh::LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value) as *mut leanh::LeanObject,10226104227652591212 as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5_value
) as *mut leanh::LeanObject;
pub unsafe fn l_instForInOfForIn_x27___redArg___lam__0(
    mut v_f_860_: *mut leanh::LeanObject,
    mut v_a_861_: *mut leanh::LeanObject,
    mut v_x_862_: *mut leanh::LeanObject,
    mut v___y_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = leanh::lean_apply_2(v_f_860_, v_a_861_, v___y_863_);
    return v___x_864_;
}
pub unsafe fn l_instForInOfForIn_x27___redArg___lam__1(
    mut v_inst_865_: *mut leanh::LeanObject,
    mut v_00_u03b2_866_: *mut leanh::LeanObject,
    mut v_x_867_: *mut leanh::LeanObject,
    mut v_b_868_: *mut leanh::LeanObject,
    mut v_f_869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_870_ = leanh::lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_870_, 0, v_f_869_);
    v___x_871_ = leanh::lean_apply_4(
        v_inst_865_,
        leanh::lean_box(0),
        v_x_867_,
        v_b_868_,
        v___f_870_,
    );
    return v___x_871_;
}
pub unsafe fn l_instForInOfForIn_x27___redArg(
    mut v_inst_872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_873_ = leanh::lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_873_, 0, v_inst_872_);
    return v___f_873_;
}
pub unsafe fn l_instForInOfForIn_x27(
    mut v_m_874_: *mut leanh::LeanObject,
    mut v_00_u03c1_875_: *mut leanh::LeanObject,
    mut v_00_u03b1_876_: *mut leanh::LeanObject,
    mut v_d_877_: *mut leanh::LeanObject,
    mut v_inst_878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_879_ = leanh::lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_879_, 0, v_inst_878_);
    return v___f_879_;
}
pub unsafe fn l_ForInStep_value___redArg(
    mut v_x_880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_881_ = leanh::lean_ctor_get(v_x_880_, 0);
    leanh::lean_inc(v_a_881_);
    return v_a_881_;
}
pub unsafe fn l_ForInStep_value___redArg___boxed(
    mut v_x_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_883_ = l_ForInStep_value___redArg(v_x_882_);
    leanh::lean_dec_ref(v_x_882_);
    return v_res_883_;
}
pub unsafe fn l_ForInStep_value(
    mut v_00_u03b1_884_: *mut leanh::LeanObject,
    mut v_x_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_886_ = leanh::lean_ctor_get(v_x_885_, 0);
    leanh::lean_inc(v_a_886_);
    return v_a_886_;
}
pub unsafe fn l_ForInStep_value___boxed(
    mut v_00_u03b1_887_: *mut leanh::LeanObject,
    mut v_x_888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_889_ = l_ForInStep_value(v_00_u03b1_887_, v_x_888_);
    leanh::lean_dec_ref(v_x_888_);
    return v_res_889_;
}
pub unsafe fn l_Functor_mapRev___redArg(
    mut v_inst_890_: *mut leanh::LeanObject,
    mut v_a_891_: *mut leanh::LeanObject,
    mut v_f_892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_893_ = leanh::lean_ctor_get(v_inst_890_, 0);
    leanh::lean_inc(v_map_893_);
    leanh::lean_dec_ref(v_inst_890_);
    v___x_894_ = leanh::lean_apply_4(
        v_map_893_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_f_892_,
        v_a_891_,
    );
    return v___x_894_;
}
pub unsafe fn l_Functor_mapRev(
    mut v_f_895_: *mut leanh::LeanObject,
    mut v_inst_896_: *mut leanh::LeanObject,
    mut v_00_u03b1_897_: *mut leanh::LeanObject,
    mut v_00_u03b2_898_: *mut leanh::LeanObject,
    mut v_a_899_: *mut leanh::LeanObject,
    mut v_f_900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_901_ = l_Functor_mapRev___redArg(v_inst_896_, v_a_899_, v_f_900_);
    return v___x_901_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_937_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5;
    v___x_938_ = l_String_toRawSubstring_x27(v___x_937_);
    return v___x_938_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1(
    mut v_x_953_: *mut leanh::LeanObject,
    mut v_a_954_: *mut leanh::LeanObject,
    mut v_a_955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u8 = 0;
    v___x_956_ = l_term___x3c_x26_x3e___00__closed__1;
    leanh::lean_inc(v_x_953_);
    v___x_957_ = l_Lean_Syntax_isOfKind(v_x_953_, v___x_956_);
    if v___x_957_ == 0 {
        let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_953_);
        v___x_958_ = leanh::lean_box(1);
        v___x_959_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_959_, 0, v___x_958_);
        leanh::lean_ctor_set(v___x_959_, 1, v_a_955_);
        return v___x_959_;
    } else {
        let mut v_quotContext_960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: u8 = 0;
        let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_960_ = leanh::lean_ctor_get(v_a_954_, 1);
        v_currMacroScope_961_ = leanh::lean_ctor_get(v_a_954_, 2);
        v_ref_962_ = leanh::lean_ctor_get(v_a_954_, 5);
        v___x_963_ = leanh::lean_unsigned_to_nat(0);
        v___x_964_ = l_Lean_Syntax_getArg(v_x_953_, v___x_963_);
        v___x_965_ = leanh::lean_unsigned_to_nat(2);
        v___x_966_ = l_Lean_Syntax_getArg(v_x_953_, v___x_965_);
        leanh::lean_dec(v_x_953_);
        v___x_967_ = 0;
        v___x_968_ = l_Lean_SourceInfo_fromRef(v_ref_962_, v___x_967_);
        v___x_969_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_970_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6);
        v___x_971_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9;
        leanh::lean_inc(v_currMacroScope_961_);
        leanh::lean_inc(v_quotContext_960_);
        v___x_972_ = l_Lean_addMacroScope(v_quotContext_960_, v___x_971_, v_currMacroScope_961_);
        v___x_973_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11;
        leanh::lean_inc_n(v___x_968_, 2);
        v___x_974_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_974_, 0, v___x_968_);
        leanh::lean_ctor_set(v___x_974_, 1, v___x_970_);
        leanh::lean_ctor_set(v___x_974_, 2, v___x_972_);
        leanh::lean_ctor_set(v___x_974_, 3, v___x_973_);
        v___x_975_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_976_ = l_Lean_Syntax_node2(v___x_968_, v___x_975_, v___x_964_, v___x_966_);
        v___x_977_ = l_Lean_Syntax_node2(v___x_968_, v___x_969_, v___x_974_, v___x_976_);
        v___x_978_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_978_, 0, v___x_977_);
        leanh::lean_ctor_set(v___x_978_, 1, v_a_955_);
        return v___x_978_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___boxed(
    mut v_x_979_: *mut leanh::LeanObject,
    mut v_a_980_: *mut leanh::LeanObject,
    mut v_a_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1(
        v_x_979_, v_a_980_, v_a_981_,
    );
    leanh::lean_dec_ref(v_a_980_);
    return v_res_982_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(
    mut v_x_986_: *mut leanh::LeanObject,
    mut v_a_987_: *mut leanh::LeanObject,
    mut v_a_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    v___x_989_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    leanh::lean_inc(v_x_986_);
    v___x_990_ = l_Lean_Syntax_isOfKind(v_x_986_, v___x_989_);
    if v___x_990_ == 0 {
        let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_986_);
        v___x_991_ = leanh::lean_box(0);
        v___x_992_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_992_, 0, v___x_991_);
        leanh::lean_ctor_set(v___x_992_, 1, v_a_988_);
        return v___x_992_;
    } else {
        let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_996_: u8 = 0;
        v___x_993_ = leanh::lean_unsigned_to_nat(0);
        v___x_994_ = l_Lean_Syntax_getArg(v_x_986_, v___x_993_);
        v___x_995_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        leanh::lean_inc(v___x_994_);
        v___x_996_ = l_Lean_Syntax_isOfKind(v___x_994_, v___x_995_);
        if v___x_996_ == 0 {
            let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_994_);
            leanh::lean_dec(v_x_986_);
            v___x_997_ = leanh::lean_box(0);
            v___x_998_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_998_, 0, v___x_997_);
            leanh::lean_ctor_set(v___x_998_, 1, v_a_988_);
            return v___x_998_;
        } else {
            let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1002_: u8 = 0;
            v___x_999_ = leanh::lean_unsigned_to_nat(1);
            v___x_1000_ = l_Lean_Syntax_getArg(v_x_986_, v___x_999_);
            leanh::lean_dec(v_x_986_);
            v___x_1001_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1000_);
            v___x_1002_ = l_Lean_Syntax_matchesNull(v___x_1000_, v___x_1001_);
            if v___x_1002_ == 0 {
                let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1000_);
                leanh::lean_dec(v___x_994_);
                v___x_1003_ = leanh::lean_box(0);
                v___x_1004_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1004_, 0, v___x_1003_);
                leanh::lean_ctor_set(v___x_1004_, 1, v_a_988_);
                return v___x_1004_;
            } else {
                let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1008_: u8 = 0;
                let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1005_ = l_Lean_Syntax_getArg(v___x_1000_, v___x_993_);
                v___x_1006_ = l_Lean_Syntax_getArg(v___x_1000_, v___x_999_);
                leanh::lean_dec(v___x_1000_);
                v_ref_1007_ = l_Lean_replaceRef(v___x_994_, v_a_987_);
                leanh::lean_dec(v___x_994_);
                v___x_1008_ = 0;
                v___x_1009_ = l_Lean_SourceInfo_fromRef(v_ref_1007_, v___x_1008_);
                leanh::lean_dec(v_ref_1007_);
                v___x_1010_ = l_term___x3c_x26_x3e___00__closed__1;
                v___x_1011_ = l_term___x3c_x26_x3e___00__closed__4;
                leanh::lean_inc(v___x_1009_);
                v___x_1012_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1012_, 0, v___x_1009_);
                leanh::lean_ctor_set(v___x_1012_, 1, v___x_1011_);
                v___x_1013_ = l_Lean_Syntax_node3(
                    v___x_1009_,
                    v___x_1010_,
                    v___x_1005_,
                    v___x_1012_,
                    v___x_1006_,
                );
                v___x_1014_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1014_, 0, v___x_1013_);
                leanh::lean_ctor_set(v___x_1014_, 1, v_a_988_);
                return v___x_1014_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___boxed(
    mut v_x_1015_: *mut leanh::LeanObject,
    mut v_a_1016_: *mut leanh::LeanObject,
    mut v_a_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(
        v_x_1015_, v_a_1016_, v_a_1017_,
    );
    leanh::lean_dec(v_a_1016_);
    return v_res_1018_;
}
pub unsafe fn l_Functor_discard___redArg(
    mut v_inst_1019_: *mut leanh::LeanObject,
    mut v_x_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mapConst_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mapConst_1021_ = leanh::lean_ctor_get(v_inst_1019_, 1);
    leanh::lean_inc(v_mapConst_1021_);
    leanh::lean_dec_ref(v_inst_1019_);
    v___x_1022_ = leanh::lean_box(0);
    v___x_1023_ = leanh::lean_apply_4(
        v_mapConst_1021_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1022_,
        v_x_1020_,
    );
    return v___x_1023_;
}
pub unsafe fn l_Functor_discard(
    mut v_f_1024_: *mut leanh::LeanObject,
    mut v_00_u03b1_1025_: *mut leanh::LeanObject,
    mut v_inst_1026_: *mut leanh::LeanObject,
    mut v_x_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mapConst_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mapConst_1028_ = leanh::lean_ctor_get(v_inst_1026_, 1);
    leanh::lean_inc(v_mapConst_1028_);
    leanh::lean_dec_ref(v_inst_1026_);
    v___x_1029_ = leanh::lean_box(0);
    v___x_1030_ = leanh::lean_apply_4(
        v_mapConst_1028_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1029_,
        v_x_1027_,
    );
    return v___x_1030_;
}
pub unsafe fn l_instOrElseOfAlternative___redArg(
    mut v_inst_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_1032_ = leanh::lean_ctor_get(v_inst_1031_, 2);
    leanh::lean_inc(v_orElse_1032_);
    leanh::lean_dec_ref(v_inst_1031_);
    v___x_1033_ = leanh::lean_apply_1(v_orElse_1032_, leanh::lean_box(0));
    return v___x_1033_;
}
pub unsafe fn l_instOrElseOfAlternative(
    mut v_f_1034_: *mut leanh::LeanObject,
    mut v_00_u03b1_1035_: *mut leanh::LeanObject,
    mut v_inst_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_instOrElseOfAlternative___redArg(v_inst_1036_);
    return v___x_1037_;
}
pub unsafe fn l_guard___redArg(
    mut v_inst_1038_: *mut leanh::LeanObject,
    mut v_inst_1039_: u8,
) -> *mut leanh::LeanObject {
    if v_inst_1039_ == 0 {
        let mut v_failure_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_failure_1040_ = leanh::lean_ctor_get(v_inst_1038_, 1);
        leanh::lean_inc(v_failure_1040_);
        leanh::lean_dec_ref(v_inst_1038_);
        v___x_1041_ = leanh::lean_apply_1(v_failure_1040_, leanh::lean_box(0));
        return v___x_1041_;
    } else {
        let mut v_toApplicative_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1042_ = leanh::lean_ctor_get(v_inst_1038_, 0);
        leanh::lean_inc_ref(v_toApplicative_1042_);
        leanh::lean_dec_ref(v_inst_1038_);
        v_toPure_1043_ = leanh::lean_ctor_get(v_toApplicative_1042_, 1);
        leanh::lean_inc(v_toPure_1043_);
        leanh::lean_dec_ref(v_toApplicative_1042_);
        v___x_1044_ = leanh::lean_box(0);
        v___x_1045_ =
            leanh::lean_apply_2(v_toPure_1043_, leanh::lean_box(0), v___x_1044_);
        return v___x_1045_;
    }
}
pub unsafe fn l_guard___redArg___boxed(
    mut v_inst_1046_: *mut leanh::LeanObject,
    mut v_inst_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_22__boxed_1048_: u8 = 0;
    let mut v_res_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_22__boxed_1048_ = (leanh::lean_unbox(v_inst_1047_) as u8);
    v_res_1049_ = l_guard___redArg(v_inst_1046_, v_inst_22__boxed_1048_);
    return v_res_1049_;
}
pub unsafe fn l_guard(
    mut v_f_1050_: *mut leanh::LeanObject,
    mut v_inst_1051_: *mut leanh::LeanObject,
    mut v_p_1052_: *mut leanh::LeanObject,
    mut v_inst_1053_: u8,
) -> *mut leanh::LeanObject {
    if v_inst_1053_ == 0 {
        let mut v_failure_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_failure_1054_ = leanh::lean_ctor_get(v_inst_1051_, 1);
        leanh::lean_inc(v_failure_1054_);
        leanh::lean_dec_ref(v_inst_1051_);
        v___x_1055_ = leanh::lean_apply_1(v_failure_1054_, leanh::lean_box(0));
        return v___x_1055_;
    } else {
        let mut v_toApplicative_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1056_ = leanh::lean_ctor_get(v_inst_1051_, 0);
        leanh::lean_inc_ref(v_toApplicative_1056_);
        leanh::lean_dec_ref(v_inst_1051_);
        v_toPure_1057_ = leanh::lean_ctor_get(v_toApplicative_1056_, 1);
        leanh::lean_inc(v_toPure_1057_);
        leanh::lean_dec_ref(v_toApplicative_1056_);
        v___x_1058_ = leanh::lean_box(0);
        v___x_1059_ =
            leanh::lean_apply_2(v_toPure_1057_, leanh::lean_box(0), v___x_1058_);
        return v___x_1059_;
    }
}
pub unsafe fn l_guard___boxed(
    mut v_f_1060_: *mut leanh::LeanObject,
    mut v_inst_1061_: *mut leanh::LeanObject,
    mut v_p_1062_: *mut leanh::LeanObject,
    mut v_inst_1063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_34__boxed_1064_: u8 = 0;
    let mut v_res_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_34__boxed_1064_ = (leanh::lean_unbox(v_inst_1063_) as u8);
    v_res_1065_ = l_guard(v_f_1060_, v_inst_1061_, v_p_1062_, v_inst_34__boxed_1064_);
    return v_res_1065_;
}
pub unsafe fn l_optional___redArg___lam__0(
    mut v_val_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1067_, 0, v_val_1066_);
    return v___x_1067_;
}
pub unsafe fn l_optional___redArg___lam__1(
    mut v_toPure_1068_: *mut leanh::LeanObject,
    mut v_x_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = leanh::lean_box(0);
    v___x_1071_ =
        leanh::lean_apply_2(v_toPure_1068_, leanh::lean_box(0), v___x_1070_);
    return v___x_1071_;
}
pub unsafe fn l_optional___redArg(
    mut v_inst_1073_: *mut leanh::LeanObject,
    mut v_x_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_orElse_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1075_ = leanh::lean_ctor_get(v_inst_1073_, 0);
    leanh::lean_inc_ref(v_toApplicative_1075_);
    v_toFunctor_1076_ = leanh::lean_ctor_get(v_toApplicative_1075_, 0);
    leanh::lean_inc_ref(v_toFunctor_1076_);
    v_orElse_1077_ = leanh::lean_ctor_get(v_inst_1073_, 2);
    leanh::lean_inc(v_orElse_1077_);
    leanh::lean_dec_ref(v_inst_1073_);
    v_toPure_1078_ = leanh::lean_ctor_get(v_toApplicative_1075_, 1);
    leanh::lean_inc(v_toPure_1078_);
    leanh::lean_dec_ref(v_toApplicative_1075_);
    v_map_1079_ = leanh::lean_ctor_get(v_toFunctor_1076_, 0);
    leanh::lean_inc(v_map_1079_);
    leanh::lean_dec_ref(v_toFunctor_1076_);
    v___f_1080_ = l_optional___redArg___closed__0;
    v___f_1081_ = leanh::lean_alloc_closure(
        l_optional___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1081_, 0, v_toPure_1078_);
    v___x_1082_ = leanh::lean_apply_4(
        v_map_1079_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1080_,
        v_x_1074_,
    );
    v___x_1083_ = leanh::lean_apply_3(
        v_orElse_1077_,
        leanh::lean_box(0),
        v___x_1082_,
        v___f_1081_,
    );
    return v___x_1083_;
}
pub unsafe fn l_optional(
    mut v_f_1084_: *mut leanh::LeanObject,
    mut v_inst_1085_: *mut leanh::LeanObject,
    mut v_00_u03b1_1086_: *mut leanh::LeanObject,
    mut v_x_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_orElse_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1088_ = leanh::lean_ctor_get(v_inst_1085_, 0);
    leanh::lean_inc_ref(v_toApplicative_1088_);
    v_toFunctor_1089_ = leanh::lean_ctor_get(v_toApplicative_1088_, 0);
    leanh::lean_inc_ref(v_toFunctor_1089_);
    v_orElse_1090_ = leanh::lean_ctor_get(v_inst_1085_, 2);
    leanh::lean_inc(v_orElse_1090_);
    leanh::lean_dec_ref(v_inst_1085_);
    v_toPure_1091_ = leanh::lean_ctor_get(v_toApplicative_1088_, 1);
    leanh::lean_inc(v_toPure_1091_);
    leanh::lean_dec_ref(v_toApplicative_1088_);
    v_map_1092_ = leanh::lean_ctor_get(v_toFunctor_1089_, 0);
    leanh::lean_inc(v_map_1092_);
    leanh::lean_dec_ref(v_toFunctor_1089_);
    v___f_1093_ = l_optional___redArg___closed__0;
    v___f_1094_ = leanh::lean_alloc_closure(
        l_optional___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1094_, 0, v_toPure_1091_);
    v___x_1095_ = leanh::lean_apply_4(
        v_map_1092_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1093_,
        v_x_1087_,
    );
    v___x_1096_ = leanh::lean_apply_3(
        v_orElse_1090_,
        leanh::lean_box(0),
        v___x_1095_,
        v___f_1094_,
    );
    return v___x_1096_;
}
pub unsafe fn l_instToBoolBool___lam__0(mut v_b_1097_: u8) -> u8 {
    return v_b_1097_;
}
pub unsafe fn l_instToBoolBool___lam__0___boxed(
    mut v_b_1098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1099_: u8 = 0;
    let mut v_res_1100_: u8 = 0;
    let mut v_r_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1099_ = (leanh::lean_unbox(v_b_1098_) as u8);
    v_res_1100_ = l_instToBoolBool___lam__0(v_b_boxed_1099_);
    v_r_1101_ = leanh::lean_box((v_res_1100_) as usize);
    return v_r_1101_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1124_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0;
    v___x_1125_ = l_String_toRawSubstring_x27(v___x_1124_);
    return v___x_1125_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(
    mut v_x_1134_: *mut leanh::LeanObject,
    mut v_a_1135_: *mut leanh::LeanObject,
    mut v_a_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: u8 = 0;
    v___x_1137_ = l_term___x3c_x7c_x7c_x3e___00__closed__1;
    leanh::lean_inc(v_x_1134_);
    v___x_1138_ = l_Lean_Syntax_isOfKind(v_x_1134_, v___x_1137_);
    if v___x_1138_ == 0 {
        let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1134_);
        v___x_1139_ = leanh::lean_box(1);
        v___x_1140_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1140_, 0, v___x_1139_);
        leanh::lean_ctor_set(v___x_1140_, 1, v_a_1136_);
        return v___x_1140_;
    } else {
        let mut v_quotContext_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1148_: u8 = 0;
        let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1141_ = leanh::lean_ctor_get(v_a_1135_, 1);
        v_currMacroScope_1142_ = leanh::lean_ctor_get(v_a_1135_, 2);
        v_ref_1143_ = leanh::lean_ctor_get(v_a_1135_, 5);
        v___x_1144_ = leanh::lean_unsigned_to_nat(0);
        v___x_1145_ = l_Lean_Syntax_getArg(v_x_1134_, v___x_1144_);
        v___x_1146_ = leanh::lean_unsigned_to_nat(2);
        v___x_1147_ = l_Lean_Syntax_getArg(v_x_1134_, v___x_1146_);
        leanh::lean_dec(v_x_1134_);
        v___x_1148_ = 0;
        v___x_1149_ = l_Lean_SourceInfo_fromRef(v_ref_1143_, v___x_1148_);
        v___x_1150_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1151_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1);
        v___x_1152_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2;
        leanh::lean_inc(v_currMacroScope_1142_);
        leanh::lean_inc(v_quotContext_1141_);
        v___x_1153_ =
            l_Lean_addMacroScope(v_quotContext_1141_, v___x_1152_, v_currMacroScope_1142_);
        v___x_1154_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4;
        leanh::lean_inc_n(v___x_1149_, 2);
        v___x_1155_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1155_, 0, v___x_1149_);
        leanh::lean_ctor_set(v___x_1155_, 1, v___x_1151_);
        leanh::lean_ctor_set(v___x_1155_, 2, v___x_1153_);
        leanh::lean_ctor_set(v___x_1155_, 3, v___x_1154_);
        v___x_1156_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1157_ = l_Lean_Syntax_node2(v___x_1149_, v___x_1156_, v___x_1145_, v___x_1147_);
        v___x_1158_ = l_Lean_Syntax_node2(v___x_1149_, v___x_1150_, v___x_1155_, v___x_1157_);
        v___x_1159_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1159_, 0, v___x_1158_);
        leanh::lean_ctor_set(v___x_1159_, 1, v_a_1136_);
        return v___x_1159_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___boxed(
    mut v_x_1160_: *mut leanh::LeanObject,
    mut v_a_1161_: *mut leanh::LeanObject,
    mut v_a_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1163_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(
        v_x_1160_, v_a_1161_, v_a_1162_,
    );
    leanh::lean_dec_ref(v_a_1161_);
    return v_res_1163_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__orM__1(
    mut v_x_1164_: *mut leanh::LeanObject,
    mut v_a_1165_: *mut leanh::LeanObject,
    mut v_a_1166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u8 = 0;
    v___x_1167_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    leanh::lean_inc(v_x_1164_);
    v___x_1168_ = l_Lean_Syntax_isOfKind(v_x_1164_, v___x_1167_);
    if v___x_1168_ == 0 {
        let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1164_);
        v___x_1169_ = leanh::lean_box(0);
        v___x_1170_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1170_, 0, v___x_1169_);
        leanh::lean_ctor_set(v___x_1170_, 1, v_a_1166_);
        return v___x_1170_;
    } else {
        let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: u8 = 0;
        v___x_1171_ = leanh::lean_unsigned_to_nat(0);
        v___x_1172_ = l_Lean_Syntax_getArg(v_x_1164_, v___x_1171_);
        v___x_1173_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        leanh::lean_inc(v___x_1172_);
        v___x_1174_ = l_Lean_Syntax_isOfKind(v___x_1172_, v___x_1173_);
        if v___x_1174_ == 0 {
            let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1172_);
            leanh::lean_dec(v_x_1164_);
            v___x_1175_ = leanh::lean_box(0);
            v___x_1176_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1176_, 0, v___x_1175_);
            leanh::lean_ctor_set(v___x_1176_, 1, v_a_1166_);
            return v___x_1176_;
        } else {
            let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1180_: u8 = 0;
            v___x_1177_ = leanh::lean_unsigned_to_nat(1);
            v___x_1178_ = l_Lean_Syntax_getArg(v_x_1164_, v___x_1177_);
            leanh::lean_dec(v_x_1164_);
            v___x_1179_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1178_);
            v___x_1180_ = l_Lean_Syntax_matchesNull(v___x_1178_, v___x_1179_);
            if v___x_1180_ == 0 {
                let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1178_);
                leanh::lean_dec(v___x_1172_);
                v___x_1181_ = leanh::lean_box(0);
                v___x_1182_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1182_, 0, v___x_1181_);
                leanh::lean_ctor_set(v___x_1182_, 1, v_a_1166_);
                return v___x_1182_;
            } else {
                let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1186_: u8 = 0;
                let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1183_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_1171_);
                v___x_1184_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_1177_);
                leanh::lean_dec(v___x_1178_);
                v_ref_1185_ = l_Lean_replaceRef(v___x_1172_, v_a_1165_);
                leanh::lean_dec(v___x_1172_);
                v___x_1186_ = 0;
                v___x_1187_ = l_Lean_SourceInfo_fromRef(v_ref_1185_, v___x_1186_);
                leanh::lean_dec(v_ref_1185_);
                v___x_1188_ = l_term___x3c_x7c_x7c_x3e___00__closed__1;
                v___x_1189_ = l_term___x3c_x7c_x7c_x3e___00__closed__2;
                leanh::lean_inc(v___x_1187_);
                v___x_1190_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1190_, 0, v___x_1187_);
                leanh::lean_ctor_set(v___x_1190_, 1, v___x_1189_);
                v___x_1191_ = l_Lean_Syntax_node3(
                    v___x_1187_,
                    v___x_1188_,
                    v___x_1183_,
                    v___x_1190_,
                    v___x_1184_,
                );
                v___x_1192_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1192_, 0, v___x_1191_);
                leanh::lean_ctor_set(v___x_1192_, 1, v_a_1166_);
                return v___x_1192_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__orM__1___boxed(
    mut v_x_1193_: *mut leanh::LeanObject,
    mut v_a_1194_: *mut leanh::LeanObject,
    mut v_a_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ =
        l___aux__Init__Control__Basic______unexpand__orM__1(v_x_1193_, v_a_1194_, v_a_1195_);
    leanh::lean_dec(v_a_1194_);
    return v_res_1196_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0;
    v___x_1218_ = l_String_toRawSubstring_x27(v___x_1217_);
    return v___x_1218_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(
    mut v_x_1227_: *mut leanh::LeanObject,
    mut v_a_1228_: *mut leanh::LeanObject,
    mut v_a_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: u8 = 0;
    v___x_1230_ = l_term___x3c_x26_x26_x3e___00__closed__1;
    leanh::lean_inc(v_x_1227_);
    v___x_1231_ = l_Lean_Syntax_isOfKind(v_x_1227_, v___x_1230_);
    if v___x_1231_ == 0 {
        let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1227_);
        v___x_1232_ = leanh::lean_box(1);
        v___x_1233_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1233_, 0, v___x_1232_);
        leanh::lean_ctor_set(v___x_1233_, 1, v_a_1229_);
        return v___x_1233_;
    } else {
        let mut v_quotContext_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: u8 = 0;
        let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1234_ = leanh::lean_ctor_get(v_a_1228_, 1);
        v_currMacroScope_1235_ = leanh::lean_ctor_get(v_a_1228_, 2);
        v_ref_1236_ = leanh::lean_ctor_get(v_a_1228_, 5);
        v___x_1237_ = leanh::lean_unsigned_to_nat(0);
        v___x_1238_ = l_Lean_Syntax_getArg(v_x_1227_, v___x_1237_);
        v___x_1239_ = leanh::lean_unsigned_to_nat(2);
        v___x_1240_ = l_Lean_Syntax_getArg(v_x_1227_, v___x_1239_);
        leanh::lean_dec(v_x_1227_);
        v___x_1241_ = 0;
        v___x_1242_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1241_);
        v___x_1243_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1244_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1);
        v___x_1245_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2;
        leanh::lean_inc(v_currMacroScope_1235_);
        leanh::lean_inc(v_quotContext_1234_);
        v___x_1246_ =
            l_Lean_addMacroScope(v_quotContext_1234_, v___x_1245_, v_currMacroScope_1235_);
        v___x_1247_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4;
        leanh::lean_inc_n(v___x_1242_, 2);
        v___x_1248_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1248_, 0, v___x_1242_);
        leanh::lean_ctor_set(v___x_1248_, 1, v___x_1244_);
        leanh::lean_ctor_set(v___x_1248_, 2, v___x_1246_);
        leanh::lean_ctor_set(v___x_1248_, 3, v___x_1247_);
        v___x_1249_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1250_ = l_Lean_Syntax_node2(v___x_1242_, v___x_1249_, v___x_1238_, v___x_1240_);
        v___x_1251_ = l_Lean_Syntax_node2(v___x_1242_, v___x_1243_, v___x_1248_, v___x_1250_);
        v___x_1252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1252_, 0, v___x_1251_);
        leanh::lean_ctor_set(v___x_1252_, 1, v_a_1229_);
        return v___x_1252_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___boxed(
    mut v_x_1253_: *mut leanh::LeanObject,
    mut v_a_1254_: *mut leanh::LeanObject,
    mut v_a_1255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1256_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(
        v_x_1253_, v_a_1254_, v_a_1255_,
    );
    leanh::lean_dec_ref(v_a_1254_);
    return v_res_1256_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__andM__1(
    mut v_x_1257_: *mut leanh::LeanObject,
    mut v_a_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: u8 = 0;
    v___x_1260_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    leanh::lean_inc(v_x_1257_);
    v___x_1261_ = l_Lean_Syntax_isOfKind(v_x_1257_, v___x_1260_);
    if v___x_1261_ == 0 {
        let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1257_);
        v___x_1262_ = leanh::lean_box(0);
        v___x_1263_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1263_, 0, v___x_1262_);
        leanh::lean_ctor_set(v___x_1263_, 1, v_a_1259_);
        return v___x_1263_;
    } else {
        let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: u8 = 0;
        v___x_1264_ = leanh::lean_unsigned_to_nat(0);
        v___x_1265_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1264_);
        v___x_1266_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        leanh::lean_inc(v___x_1265_);
        v___x_1267_ = l_Lean_Syntax_isOfKind(v___x_1265_, v___x_1266_);
        if v___x_1267_ == 0 {
            let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1265_);
            leanh::lean_dec(v_x_1257_);
            v___x_1268_ = leanh::lean_box(0);
            v___x_1269_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1269_, 0, v___x_1268_);
            leanh::lean_ctor_set(v___x_1269_, 1, v_a_1259_);
            return v___x_1269_;
        } else {
            let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1273_: u8 = 0;
            v___x_1270_ = leanh::lean_unsigned_to_nat(1);
            v___x_1271_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1270_);
            leanh::lean_dec(v_x_1257_);
            v___x_1272_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1271_);
            v___x_1273_ = l_Lean_Syntax_matchesNull(v___x_1271_, v___x_1272_);
            if v___x_1273_ == 0 {
                let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1271_);
                leanh::lean_dec(v___x_1265_);
                v___x_1274_ = leanh::lean_box(0);
                v___x_1275_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1275_, 0, v___x_1274_);
                leanh::lean_ctor_set(v___x_1275_, 1, v_a_1259_);
                return v___x_1275_;
            } else {
                let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1279_: u8 = 0;
                let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1276_ = l_Lean_Syntax_getArg(v___x_1271_, v___x_1264_);
                v___x_1277_ = l_Lean_Syntax_getArg(v___x_1271_, v___x_1270_);
                leanh::lean_dec(v___x_1271_);
                v_ref_1278_ = l_Lean_replaceRef(v___x_1265_, v_a_1258_);
                leanh::lean_dec(v___x_1265_);
                v___x_1279_ = 0;
                v___x_1280_ = l_Lean_SourceInfo_fromRef(v_ref_1278_, v___x_1279_);
                leanh::lean_dec(v_ref_1278_);
                v___x_1281_ = l_term___x3c_x26_x26_x3e___00__closed__1;
                v___x_1282_ = l_term___x3c_x26_x26_x3e___00__closed__2;
                leanh::lean_inc(v___x_1280_);
                v___x_1283_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1283_, 0, v___x_1280_);
                leanh::lean_ctor_set(v___x_1283_, 1, v___x_1282_);
                v___x_1284_ = l_Lean_Syntax_node3(
                    v___x_1280_,
                    v___x_1281_,
                    v___x_1276_,
                    v___x_1283_,
                    v___x_1277_,
                );
                v___x_1285_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1285_, 0, v___x_1284_);
                leanh::lean_ctor_set(v___x_1285_, 1, v_a_1259_);
                return v___x_1285_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__andM__1___boxed(
    mut v_x_1286_: *mut leanh::LeanObject,
    mut v_a_1287_: *mut leanh::LeanObject,
    mut v_a_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ =
        l___aux__Init__Control__Basic______unexpand__andM__1(v_x_1286_, v_a_1287_, v_a_1288_);
    leanh::lean_dec(v_a_1287_);
    return v_res_1289_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__0(
    mut v_x_u2082_1290_: *mut leanh::LeanObject,
    mut v_x_u2081_1291_: *mut leanh::LeanObject,
    mut v_00_u03b2_1292_: *mut leanh::LeanObject,
    mut v___y_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ =
        leanh::lean_apply_2(v_x_u2082_1290_, leanh::lean_box(0), v___y_1293_);
    v___x_1295_ =
        leanh::lean_apply_2(v_x_u2081_1291_, leanh::lean_box(0), v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__1(
    mut v_x_u2082_1296_: *mut leanh::LeanObject,
    mut v_f_1297_: *mut leanh::LeanObject,
    mut v_x_u2081_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1299_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1299_, 0, v_x_u2082_1296_);
    leanh::lean_closure_set(v___f_1299_, 1, v_x_u2081_1298_);
    v___x_1300_ = leanh::lean_apply_1(v_f_1297_, v___f_1299_);
    return v___x_1300_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__2(
    mut v_inst_1301_: *mut leanh::LeanObject,
    mut v_f_1302_: *mut leanh::LeanObject,
    mut v_x_u2082_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_liftWith_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1304_ = leanh::lean_ctor_get(v_inst_1301_, 0);
    leanh::lean_inc(v_liftWith_1304_);
    leanh::lean_dec_ref(v_inst_1301_);
    v___f_1305_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1305_, 0, v_x_u2082_1303_);
    leanh::lean_closure_set(v___f_1305_, 1, v_f_1302_);
    v___x_1306_ =
        leanh::lean_apply_2(v_liftWith_1304_, leanh::lean_box(0), v___f_1305_);
    return v___x_1306_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__3(
    mut v_inst_1307_: *mut leanh::LeanObject,
    mut v_inst_1308_: *mut leanh::LeanObject,
    mut v_00_u03b1_1309_: *mut leanh::LeanObject,
    mut v_f_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_liftWith_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1311_ = leanh::lean_ctor_get(v_inst_1307_, 0);
    leanh::lean_inc(v_liftWith_1311_);
    leanh::lean_dec_ref(v_inst_1307_);
    v___f_1312_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1312_, 0, v_inst_1308_);
    leanh::lean_closure_set(v___f_1312_, 1, v_f_1310_);
    v___x_1313_ =
        leanh::lean_apply_2(v_liftWith_1311_, leanh::lean_box(0), v___f_1312_);
    return v___x_1313_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__4(
    mut v_inst_1314_: *mut leanh::LeanObject,
    mut v_inst_1315_: *mut leanh::LeanObject,
    mut v_00_u03b1_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_restoreM_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_restoreM_1318_ = leanh::lean_ctor_get(v_inst_1314_, 1);
    leanh::lean_inc(v_restoreM_1318_);
    leanh::lean_dec_ref(v_inst_1314_);
    v_restoreM_1319_ = leanh::lean_ctor_get(v_inst_1315_, 1);
    leanh::lean_inc(v_restoreM_1319_);
    leanh::lean_dec_ref(v_inst_1315_);
    v___x_1320_ =
        leanh::lean_apply_2(v_restoreM_1319_, leanh::lean_box(0), v___y_1317_);
    v___x_1321_ =
        leanh::lean_apply_2(v_restoreM_1318_, leanh::lean_box(0), v___x_1320_);
    return v___x_1321_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg(
    mut v_inst_1322_: *mut leanh::LeanObject,
    mut v_inst_1323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1323_);
    leanh::lean_inc_ref(v_inst_1322_);
    v___f_1324_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1324_, 0, v_inst_1322_);
    leanh::lean_closure_set(v___f_1324_, 1, v_inst_1323_);
    v___f_1325_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1325_, 0, v_inst_1322_);
    leanh::lean_closure_set(v___f_1325_, 1, v_inst_1323_);
    v___x_1326_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1326_, 0, v___f_1324_);
    leanh::lean_ctor_set(v___x_1326_, 1, v___f_1325_);
    return v___x_1326_;
}
pub unsafe fn l_instMonadControlTOfMonadControl(
    mut v_m_1327_: *mut leanh::LeanObject,
    mut v_n_1328_: *mut leanh::LeanObject,
    mut v_o_1329_: *mut leanh::LeanObject,
    mut v_inst_1330_: *mut leanh::LeanObject,
    mut v_inst_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1331_);
    leanh::lean_inc_ref(v_inst_1330_);
    v___f_1332_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1332_, 0, v_inst_1330_);
    leanh::lean_closure_set(v___f_1332_, 1, v_inst_1331_);
    v___f_1333_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1333_, 0, v_inst_1330_);
    leanh::lean_closure_set(v___f_1333_, 1, v_inst_1331_);
    v___x_1334_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1334_, 0, v___f_1332_);
    leanh::lean_ctor_set(v___x_1334_, 1, v___f_1333_);
    return v___x_1334_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__0(
    mut v_00_u03b2_1335_: *mut leanh::LeanObject,
    mut v_x_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_1336_);
    return v_x_1336_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__0___boxed(
    mut v_00_u03b2_1337_: *mut leanh::LeanObject,
    mut v_x_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1339_ = l_instMonadControlTOfPure___redArg___lam__0(v_00_u03b2_1337_, v_x_1338_);
    leanh::lean_dec(v_x_1338_);
    return v_res_1339_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__1(
    mut v___f_1340_: *mut leanh::LeanObject,
    mut v_00_u03b1_1341_: *mut leanh::LeanObject,
    mut v_f_1342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = leanh::lean_apply_1(v_f_1342_, v___f_1340_);
    return v___x_1343_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__2(
    mut v_inst_1344_: *mut leanh::LeanObject,
    mut v_00_u03b1_1345_: *mut leanh::LeanObject,
    mut v_x_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = leanh::lean_apply_2(v_inst_1344_, leanh::lean_box(0), v_x_1346_);
    return v___x_1347_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg(
    mut v_inst_1351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1352_ = l_instMonadControlTOfPure___redArg___closed__1;
    v___f_1353_ = leanh::lean_alloc_closure(
        l_instMonadControlTOfPure___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1353_, 0, v_inst_1351_);
    v___x_1354_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1354_, 0, v___f_1352_);
    leanh::lean_ctor_set(v___x_1354_, 1, v___f_1353_);
    return v___x_1354_;
}
pub unsafe fn l_instMonadControlTOfPure(
    mut v_m_1355_: *mut leanh::LeanObject,
    mut v_inst_1356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_instMonadControlTOfPure___redArg(v_inst_1356_);
    return v___x_1357_;
}
pub unsafe fn l_controlAt___redArg(
    mut v_inst_1358_: *mut leanh::LeanObject,
    mut v_inst_1359_: *mut leanh::LeanObject,
    mut v_f_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_liftWith_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1361_ = leanh::lean_ctor_get(v_inst_1358_, 0);
    leanh::lean_inc(v_liftWith_1361_);
    v_restoreM_1362_ = leanh::lean_ctor_get(v_inst_1358_, 1);
    leanh::lean_inc(v_restoreM_1362_);
    leanh::lean_dec_ref(v_inst_1358_);
    v___x_1363_ =
        leanh::lean_apply_2(v_liftWith_1361_, leanh::lean_box(0), v_f_1360_);
    v___x_1364_ = leanh::lean_apply_1(v_restoreM_1362_, leanh::lean_box(0));
    v___x_1365_ = leanh::lean_apply_4(
        v_inst_1359_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1363_,
        v___x_1364_,
    );
    return v___x_1365_;
}
pub unsafe fn l_controlAt(
    mut v_m_1366_: *mut leanh::LeanObject,
    mut v_n_1367_: *mut leanh::LeanObject,
    mut v_inst_1368_: *mut leanh::LeanObject,
    mut v_inst_1369_: *mut leanh::LeanObject,
    mut v_00_u03b1_1370_: *mut leanh::LeanObject,
    mut v_f_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_liftWith_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1372_ = leanh::lean_ctor_get(v_inst_1368_, 0);
    leanh::lean_inc(v_liftWith_1372_);
    v_restoreM_1373_ = leanh::lean_ctor_get(v_inst_1368_, 1);
    leanh::lean_inc(v_restoreM_1373_);
    leanh::lean_dec_ref(v_inst_1368_);
    v___x_1374_ =
        leanh::lean_apply_2(v_liftWith_1372_, leanh::lean_box(0), v_f_1371_);
    v___x_1375_ = leanh::lean_apply_1(v_restoreM_1373_, leanh::lean_box(0));
    v___x_1376_ = leanh::lean_apply_4(
        v_inst_1369_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1374_,
        v___x_1375_,
    );
    return v___x_1376_;
}
pub unsafe fn l_control___redArg(
    mut v_inst_1377_: *mut leanh::LeanObject,
    mut v_inst_1378_: *mut leanh::LeanObject,
    mut v_f_1379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_liftWith_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1380_ = leanh::lean_ctor_get(v_inst_1377_, 0);
    leanh::lean_inc(v_liftWith_1380_);
    v_restoreM_1381_ = leanh::lean_ctor_get(v_inst_1377_, 1);
    leanh::lean_inc(v_restoreM_1381_);
    leanh::lean_dec_ref(v_inst_1377_);
    v___x_1382_ =
        leanh::lean_apply_2(v_liftWith_1380_, leanh::lean_box(0), v_f_1379_);
    v___x_1383_ = leanh::lean_apply_1(v_restoreM_1381_, leanh::lean_box(0));
    v___x_1384_ = leanh::lean_apply_4(
        v_inst_1378_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1382_,
        v___x_1383_,
    );
    return v___x_1384_;
}
pub unsafe fn l_control(
    mut v_m_1385_: *mut leanh::LeanObject,
    mut v_n_1386_: *mut leanh::LeanObject,
    mut v_inst_1387_: *mut leanh::LeanObject,
    mut v_inst_1388_: *mut leanh::LeanObject,
    mut v_00_u03b1_1389_: *mut leanh::LeanObject,
    mut v_f_1390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_liftWith_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_liftWith_1391_ = leanh::lean_ctor_get(v_inst_1387_, 0);
    leanh::lean_inc(v_liftWith_1391_);
    v_restoreM_1392_ = leanh::lean_ctor_get(v_inst_1387_, 1);
    leanh::lean_inc(v_restoreM_1392_);
    leanh::lean_dec_ref(v_inst_1387_);
    v___x_1393_ =
        leanh::lean_apply_2(v_liftWith_1391_, leanh::lean_box(0), v_f_1390_);
    v___x_1394_ = leanh::lean_apply_1(v_restoreM_1392_, leanh::lean_box(0));
    v___x_1395_ = leanh::lean_apply_4(
        v_inst_1388_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1393_,
        v___x_1394_,
    );
    return v___x_1395_;
}
pub unsafe fn l_Bind_kleisliRight___redArg(
    mut v_inst_1396_: *mut leanh::LeanObject,
    mut v_f_u2081_1397_: *mut leanh::LeanObject,
    mut v_f_u2082_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = leanh::lean_apply_1(v_f_u2081_1397_, v_a_1399_);
    v___x_1401_ = leanh::lean_apply_4(
        v_inst_1396_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1400_,
        v_f_u2082_1398_,
    );
    return v___x_1401_;
}
pub unsafe fn l_Bind_kleisliRight(
    mut v_00_u03b1_1402_: *mut leanh::LeanObject,
    mut v_m_1403_: *mut leanh::LeanObject,
    mut v_00_u03b2_1404_: *mut leanh::LeanObject,
    mut v_00_u03b3_1405_: *mut leanh::LeanObject,
    mut v_inst_1406_: *mut leanh::LeanObject,
    mut v_f_u2081_1407_: *mut leanh::LeanObject,
    mut v_f_u2082_1408_: *mut leanh::LeanObject,
    mut v_a_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = leanh::lean_apply_1(v_f_u2081_1407_, v_a_1409_);
    v___x_1411_ = leanh::lean_apply_4(
        v_inst_1406_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1410_,
        v_f_u2082_1408_,
    );
    return v___x_1411_;
}
pub unsafe fn l_Bind_kleisliLeft___redArg(
    mut v_inst_1412_: *mut leanh::LeanObject,
    mut v_f_u2082_1413_: *mut leanh::LeanObject,
    mut v_f_u2081_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = leanh::lean_apply_1(v_f_u2081_1414_, v_a_1415_);
    v___x_1417_ = leanh::lean_apply_4(
        v_inst_1412_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1416_,
        v_f_u2082_1413_,
    );
    return v___x_1417_;
}
pub unsafe fn l_Bind_kleisliLeft(
    mut v_00_u03b1_1418_: *mut leanh::LeanObject,
    mut v_m_1419_: *mut leanh::LeanObject,
    mut v_00_u03b2_1420_: *mut leanh::LeanObject,
    mut v_00_u03b3_1421_: *mut leanh::LeanObject,
    mut v_inst_1422_: *mut leanh::LeanObject,
    mut v_f_u2082_1423_: *mut leanh::LeanObject,
    mut v_f_u2081_1424_: *mut leanh::LeanObject,
    mut v_a_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = leanh::lean_apply_1(v_f_u2081_1424_, v_a_1425_);
    v___x_1427_ = leanh::lean_apply_4(
        v_inst_1422_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1426_,
        v_f_u2082_1423_,
    );
    return v___x_1427_;
}
pub unsafe fn l_Bind_bindLeft___redArg(
    mut v_inst_1428_: *mut leanh::LeanObject,
    mut v_f_1429_: *mut leanh::LeanObject,
    mut v_ma_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = leanh::lean_apply_4(
        v_inst_1428_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_ma_1430_,
        v_f_1429_,
    );
    return v___x_1431_;
}
pub unsafe fn l_Bind_bindLeft(
    mut v_00_u03b1_1432_: *mut leanh::LeanObject,
    mut v_m_1433_: *mut leanh::LeanObject,
    mut v_00_u03b2_1434_: *mut leanh::LeanObject,
    mut v_inst_1435_: *mut leanh::LeanObject,
    mut v_f_1436_: *mut leanh::LeanObject,
    mut v_ma_1437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = leanh::lean_apply_4(
        v_inst_1435_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_ma_1437_,
        v_f_1436_,
    );
    return v___x_1438_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ =
        l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0;
    v___x_1460_ = l_String_toRawSubstring_x27(v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(
    mut v_x_1472_: *mut leanh::LeanObject,
    mut v_a_1473_: *mut leanh::LeanObject,
    mut v_a_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    v___x_1475_ = l_term___x3e_x3d_x3e___00__closed__1;
    leanh::lean_inc(v_x_1472_);
    v___x_1476_ = l_Lean_Syntax_isOfKind(v_x_1472_, v___x_1475_);
    if v___x_1476_ == 0 {
        let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1472_);
        v___x_1477_ = leanh::lean_box(1);
        v___x_1478_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1478_, 0, v___x_1477_);
        leanh::lean_ctor_set(v___x_1478_, 1, v_a_1474_);
        return v___x_1478_;
    } else {
        let mut v_quotContext_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1486_: u8 = 0;
        let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1479_ = leanh::lean_ctor_get(v_a_1473_, 1);
        v_currMacroScope_1480_ = leanh::lean_ctor_get(v_a_1473_, 2);
        v_ref_1481_ = leanh::lean_ctor_get(v_a_1473_, 5);
        v___x_1482_ = leanh::lean_unsigned_to_nat(0);
        v___x_1483_ = l_Lean_Syntax_getArg(v_x_1472_, v___x_1482_);
        v___x_1484_ = leanh::lean_unsigned_to_nat(2);
        v___x_1485_ = l_Lean_Syntax_getArg(v_x_1472_, v___x_1484_);
        leanh::lean_dec(v_x_1472_);
        v___x_1486_ = 0;
        v___x_1487_ = l_Lean_SourceInfo_fromRef(v_ref_1481_, v___x_1486_);
        v___x_1488_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1489_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1);
        v___x_1490_ =
            l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4;
        leanh::lean_inc(v_currMacroScope_1480_);
        leanh::lean_inc(v_quotContext_1479_);
        v___x_1491_ =
            l_Lean_addMacroScope(v_quotContext_1479_, v___x_1490_, v_currMacroScope_1480_);
        v___x_1492_ =
            l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6;
        leanh::lean_inc_n(v___x_1487_, 2);
        v___x_1493_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1493_, 0, v___x_1487_);
        leanh::lean_ctor_set(v___x_1493_, 1, v___x_1489_);
        leanh::lean_ctor_set(v___x_1493_, 2, v___x_1491_);
        leanh::lean_ctor_set(v___x_1493_, 3, v___x_1492_);
        v___x_1494_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1495_ = l_Lean_Syntax_node2(v___x_1487_, v___x_1494_, v___x_1483_, v___x_1485_);
        v___x_1496_ = l_Lean_Syntax_node2(v___x_1487_, v___x_1488_, v___x_1493_, v___x_1495_);
        v___x_1497_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1497_, 0, v___x_1496_);
        leanh::lean_ctor_set(v___x_1497_, 1, v_a_1474_);
        return v___x_1497_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___boxed(
    mut v_x_1498_: *mut leanh::LeanObject,
    mut v_a_1499_: *mut leanh::LeanObject,
    mut v_a_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(
        v_x_1498_, v_a_1499_, v_a_1500_,
    );
    leanh::lean_dec_ref(v_a_1499_);
    return v_res_1501_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(
    mut v_x_1502_: *mut leanh::LeanObject,
    mut v_a_1503_: *mut leanh::LeanObject,
    mut v_a_1504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    v___x_1505_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    leanh::lean_inc(v_x_1502_);
    v___x_1506_ = l_Lean_Syntax_isOfKind(v_x_1502_, v___x_1505_);
    if v___x_1506_ == 0 {
        let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1502_);
        v___x_1507_ = leanh::lean_box(0);
        v___x_1508_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1508_, 0, v___x_1507_);
        leanh::lean_ctor_set(v___x_1508_, 1, v_a_1504_);
        return v___x_1508_;
    } else {
        let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1512_: u8 = 0;
        v___x_1509_ = leanh::lean_unsigned_to_nat(0);
        v___x_1510_ = l_Lean_Syntax_getArg(v_x_1502_, v___x_1509_);
        v___x_1511_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        leanh::lean_inc(v___x_1510_);
        v___x_1512_ = l_Lean_Syntax_isOfKind(v___x_1510_, v___x_1511_);
        if v___x_1512_ == 0 {
            let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1510_);
            leanh::lean_dec(v_x_1502_);
            v___x_1513_ = leanh::lean_box(0);
            v___x_1514_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1514_, 0, v___x_1513_);
            leanh::lean_ctor_set(v___x_1514_, 1, v_a_1504_);
            return v___x_1514_;
        } else {
            let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1518_: u8 = 0;
            v___x_1515_ = leanh::lean_unsigned_to_nat(1);
            v___x_1516_ = l_Lean_Syntax_getArg(v_x_1502_, v___x_1515_);
            leanh::lean_dec(v_x_1502_);
            v___x_1517_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1516_);
            v___x_1518_ = l_Lean_Syntax_matchesNull(v___x_1516_, v___x_1517_);
            if v___x_1518_ == 0 {
                let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1516_);
                leanh::lean_dec(v___x_1510_);
                v___x_1519_ = leanh::lean_box(0);
                v___x_1520_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                leanh::lean_ctor_set(v___x_1520_, 1, v_a_1504_);
                return v___x_1520_;
            } else {
                let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1524_: u8 = 0;
                let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1521_ = l_Lean_Syntax_getArg(v___x_1516_, v___x_1509_);
                v___x_1522_ = l_Lean_Syntax_getArg(v___x_1516_, v___x_1515_);
                leanh::lean_dec(v___x_1516_);
                v_ref_1523_ = l_Lean_replaceRef(v___x_1510_, v_a_1503_);
                leanh::lean_dec(v___x_1510_);
                v___x_1524_ = 0;
                v___x_1525_ = l_Lean_SourceInfo_fromRef(v_ref_1523_, v___x_1524_);
                leanh::lean_dec(v_ref_1523_);
                v___x_1526_ = l_term___x3e_x3d_x3e___00__closed__1;
                v___x_1527_ = l_term___x3e_x3d_x3e___00__closed__2;
                leanh::lean_inc(v___x_1525_);
                v___x_1528_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1528_, 0, v___x_1525_);
                leanh::lean_ctor_set(v___x_1528_, 1, v___x_1527_);
                v___x_1529_ = l_Lean_Syntax_node3(
                    v___x_1525_,
                    v___x_1526_,
                    v___x_1521_,
                    v___x_1528_,
                    v___x_1522_,
                );
                v___x_1530_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1530_, 0, v___x_1529_);
                leanh::lean_ctor_set(v___x_1530_, 1, v_a_1504_);
                return v___x_1530_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1___boxed(
    mut v_x_1531_: *mut leanh::LeanObject,
    mut v_a_1532_: *mut leanh::LeanObject,
    mut v_a_1533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(
        v_x_1531_, v_a_1532_, v_a_1533_,
    );
    leanh::lean_dec(v_a_1532_);
    return v_res_1534_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0;
    v___x_1553_ = l_String_toRawSubstring_x27(v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(
    mut v_x_1564_: *mut leanh::LeanObject,
    mut v_a_1565_: *mut leanh::LeanObject,
    mut v_a_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    v___x_1567_ = l_term___x3c_x3d_x3c___00__closed__1;
    leanh::lean_inc(v_x_1564_);
    v___x_1568_ = l_Lean_Syntax_isOfKind(v_x_1564_, v___x_1567_);
    if v___x_1568_ == 0 {
        let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1564_);
        v___x_1569_ = leanh::lean_box(1);
        v___x_1570_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1570_, 0, v___x_1569_);
        leanh::lean_ctor_set(v___x_1570_, 1, v_a_1566_);
        return v___x_1570_;
    } else {
        let mut v_quotContext_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: u8 = 0;
        let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1571_ = leanh::lean_ctor_get(v_a_1565_, 1);
        v_currMacroScope_1572_ = leanh::lean_ctor_get(v_a_1565_, 2);
        v_ref_1573_ = leanh::lean_ctor_get(v_a_1565_, 5);
        v___x_1574_ = leanh::lean_unsigned_to_nat(0);
        v___x_1575_ = l_Lean_Syntax_getArg(v_x_1564_, v___x_1574_);
        v___x_1576_ = leanh::lean_unsigned_to_nat(2);
        v___x_1577_ = l_Lean_Syntax_getArg(v_x_1564_, v___x_1576_);
        leanh::lean_dec(v_x_1564_);
        v___x_1578_ = 0;
        v___x_1579_ = l_Lean_SourceInfo_fromRef(v_ref_1573_, v___x_1578_);
        v___x_1580_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1581_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1);
        v___x_1582_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3;
        leanh::lean_inc(v_currMacroScope_1572_);
        leanh::lean_inc(v_quotContext_1571_);
        v___x_1583_ =
            l_Lean_addMacroScope(v_quotContext_1571_, v___x_1582_, v_currMacroScope_1572_);
        v___x_1584_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5;
        leanh::lean_inc_n(v___x_1579_, 2);
        v___x_1585_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1585_, 0, v___x_1579_);
        leanh::lean_ctor_set(v___x_1585_, 1, v___x_1581_);
        leanh::lean_ctor_set(v___x_1585_, 2, v___x_1583_);
        leanh::lean_ctor_set(v___x_1585_, 3, v___x_1584_);
        v___x_1586_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1587_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1586_, v___x_1575_, v___x_1577_);
        v___x_1588_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1580_, v___x_1585_, v___x_1587_);
        v___x_1589_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1589_, 0, v___x_1588_);
        leanh::lean_ctor_set(v___x_1589_, 1, v_a_1566_);
        return v___x_1589_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___boxed(
    mut v_x_1590_: *mut leanh::LeanObject,
    mut v_a_1591_: *mut leanh::LeanObject,
    mut v_a_1592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1593_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(
        v_x_1590_, v_a_1591_, v_a_1592_,
    );
    leanh::lean_dec_ref(v_a_1591_);
    return v_res_1593_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(
    mut v_x_1594_: *mut leanh::LeanObject,
    mut v_a_1595_: *mut leanh::LeanObject,
    mut v_a_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: u8 = 0;
    v___x_1597_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    leanh::lean_inc(v_x_1594_);
    v___x_1598_ = l_Lean_Syntax_isOfKind(v_x_1594_, v___x_1597_);
    if v___x_1598_ == 0 {
        let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1594_);
        v___x_1599_ = leanh::lean_box(0);
        v___x_1600_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1600_, 0, v___x_1599_);
        leanh::lean_ctor_set(v___x_1600_, 1, v_a_1596_);
        return v___x_1600_;
    } else {
        let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: u8 = 0;
        v___x_1601_ = leanh::lean_unsigned_to_nat(0);
        v___x_1602_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1601_);
        v___x_1603_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        leanh::lean_inc(v___x_1602_);
        v___x_1604_ = l_Lean_Syntax_isOfKind(v___x_1602_, v___x_1603_);
        if v___x_1604_ == 0 {
            let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1602_);
            leanh::lean_dec(v_x_1594_);
            v___x_1605_ = leanh::lean_box(0);
            v___x_1606_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1606_, 0, v___x_1605_);
            leanh::lean_ctor_set(v___x_1606_, 1, v_a_1596_);
            return v___x_1606_;
        } else {
            let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1610_: u8 = 0;
            v___x_1607_ = leanh::lean_unsigned_to_nat(1);
            v___x_1608_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1607_);
            leanh::lean_dec(v_x_1594_);
            v___x_1609_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1608_);
            v___x_1610_ = l_Lean_Syntax_matchesNull(v___x_1608_, v___x_1609_);
            if v___x_1610_ == 0 {
                let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1608_);
                leanh::lean_dec(v___x_1602_);
                v___x_1611_ = leanh::lean_box(0);
                v___x_1612_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1612_, 0, v___x_1611_);
                leanh::lean_ctor_set(v___x_1612_, 1, v_a_1596_);
                return v___x_1612_;
            } else {
                let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1616_: u8 = 0;
                let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1613_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1601_);
                v___x_1614_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1607_);
                leanh::lean_dec(v___x_1608_);
                v_ref_1615_ = l_Lean_replaceRef(v___x_1602_, v_a_1595_);
                leanh::lean_dec(v___x_1602_);
                v___x_1616_ = 0;
                v___x_1617_ = l_Lean_SourceInfo_fromRef(v_ref_1615_, v___x_1616_);
                leanh::lean_dec(v_ref_1615_);
                v___x_1618_ = l_term___x3c_x3d_x3c___00__closed__1;
                v___x_1619_ = l_term___x3c_x3d_x3c___00__closed__2;
                leanh::lean_inc(v___x_1617_);
                v___x_1620_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1620_, 0, v___x_1617_);
                leanh::lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                v___x_1621_ = l_Lean_Syntax_node3(
                    v___x_1617_,
                    v___x_1618_,
                    v___x_1613_,
                    v___x_1620_,
                    v___x_1614_,
                );
                v___x_1622_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1622_, 0, v___x_1621_);
                leanh::lean_ctor_set(v___x_1622_, 1, v_a_1596_);
                return v___x_1622_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1___boxed(
    mut v_x_1623_: *mut leanh::LeanObject,
    mut v_a_1624_: *mut leanh::LeanObject,
    mut v_a_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(
        v_x_1623_, v_a_1624_, v_a_1625_,
    );
    leanh::lean_dec(v_a_1624_);
    return v_res_1626_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ =
        l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0;
    v___x_1645_ = l_String_toRawSubstring_x27(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(
    mut v_x_1656_: *mut leanh::LeanObject,
    mut v_a_1657_: *mut leanh::LeanObject,
    mut v_a_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    v___x_1659_ = l_term___x3d_x3c_x3c___00__closed__1;
    leanh::lean_inc(v_x_1656_);
    v___x_1660_ = l_Lean_Syntax_isOfKind(v_x_1656_, v___x_1659_);
    if v___x_1660_ == 0 {
        let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1656_);
        v___x_1661_ = leanh::lean_box(1);
        v___x_1662_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
        leanh::lean_ctor_set(v___x_1662_, 1, v_a_1658_);
        return v___x_1662_;
    } else {
        let mut v_quotContext_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1670_: u8 = 0;
        let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1663_ = leanh::lean_ctor_get(v_a_1657_, 1);
        v_currMacroScope_1664_ = leanh::lean_ctor_get(v_a_1657_, 2);
        v_ref_1665_ = leanh::lean_ctor_get(v_a_1657_, 5);
        v___x_1666_ = leanh::lean_unsigned_to_nat(0);
        v___x_1667_ = l_Lean_Syntax_getArg(v_x_1656_, v___x_1666_);
        v___x_1668_ = leanh::lean_unsigned_to_nat(2);
        v___x_1669_ = l_Lean_Syntax_getArg(v_x_1656_, v___x_1668_);
        leanh::lean_dec(v_x_1656_);
        v___x_1670_ = 0;
        v___x_1671_ = l_Lean_SourceInfo_fromRef(v_ref_1665_, v___x_1670_);
        v___x_1672_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1673_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1);
        v___x_1674_ =
            l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3;
        leanh::lean_inc(v_currMacroScope_1664_);
        leanh::lean_inc(v_quotContext_1663_);
        v___x_1675_ =
            l_Lean_addMacroScope(v_quotContext_1663_, v___x_1674_, v_currMacroScope_1664_);
        v___x_1676_ =
            l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5;
        leanh::lean_inc_n(v___x_1671_, 2);
        v___x_1677_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1677_, 0, v___x_1671_);
        leanh::lean_ctor_set(v___x_1677_, 1, v___x_1673_);
        leanh::lean_ctor_set(v___x_1677_, 2, v___x_1675_);
        leanh::lean_ctor_set(v___x_1677_, 3, v___x_1676_);
        v___x_1678_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1679_ = l_Lean_Syntax_node2(v___x_1671_, v___x_1678_, v___x_1667_, v___x_1669_);
        v___x_1680_ = l_Lean_Syntax_node2(v___x_1671_, v___x_1672_, v___x_1677_, v___x_1679_);
        v___x_1681_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1681_, 0, v___x_1680_);
        leanh::lean_ctor_set(v___x_1681_, 1, v_a_1658_);
        return v___x_1681_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___boxed(
    mut v_x_1682_: *mut leanh::LeanObject,
    mut v_a_1683_: *mut leanh::LeanObject,
    mut v_a_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1685_ = l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(
        v_x_1682_, v_a_1683_, v_a_1684_,
    );
    leanh::lean_dec_ref(v_a_1683_);
    return v_res_1685_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(
    mut v_x_1686_: *mut leanh::LeanObject,
    mut v_a_1687_: *mut leanh::LeanObject,
    mut v_a_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    v___x_1689_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    leanh::lean_inc(v_x_1686_);
    v___x_1690_ = l_Lean_Syntax_isOfKind(v_x_1686_, v___x_1689_);
    if v___x_1690_ == 0 {
        let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1686_);
        v___x_1691_ = leanh::lean_box(0);
        v___x_1692_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1692_, 0, v___x_1691_);
        leanh::lean_ctor_set(v___x_1692_, 1, v_a_1688_);
        return v___x_1692_;
    } else {
        let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1696_: u8 = 0;
        v___x_1693_ = leanh::lean_unsigned_to_nat(0);
        v___x_1694_ = l_Lean_Syntax_getArg(v_x_1686_, v___x_1693_);
        v___x_1695_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        leanh::lean_inc(v___x_1694_);
        v___x_1696_ = l_Lean_Syntax_isOfKind(v___x_1694_, v___x_1695_);
        if v___x_1696_ == 0 {
            let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1694_);
            leanh::lean_dec(v_x_1686_);
            v___x_1697_ = leanh::lean_box(0);
            v___x_1698_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1698_, 0, v___x_1697_);
            leanh::lean_ctor_set(v___x_1698_, 1, v_a_1688_);
            return v___x_1698_;
        } else {
            let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1702_: u8 = 0;
            v___x_1699_ = leanh::lean_unsigned_to_nat(1);
            v___x_1700_ = l_Lean_Syntax_getArg(v_x_1686_, v___x_1699_);
            leanh::lean_dec(v_x_1686_);
            v___x_1701_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1700_);
            v___x_1702_ = l_Lean_Syntax_matchesNull(v___x_1700_, v___x_1701_);
            if v___x_1702_ == 0 {
                let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1700_);
                leanh::lean_dec(v___x_1694_);
                v___x_1703_ = leanh::lean_box(0);
                v___x_1704_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1704_, 0, v___x_1703_);
                leanh::lean_ctor_set(v___x_1704_, 1, v_a_1688_);
                return v___x_1704_;
            } else {
                let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1708_: u8 = 0;
                let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1705_ = l_Lean_Syntax_getArg(v___x_1700_, v___x_1693_);
                v___x_1706_ = l_Lean_Syntax_getArg(v___x_1700_, v___x_1699_);
                leanh::lean_dec(v___x_1700_);
                v_ref_1707_ = l_Lean_replaceRef(v___x_1694_, v_a_1687_);
                leanh::lean_dec(v___x_1694_);
                v___x_1708_ = 0;
                v___x_1709_ = l_Lean_SourceInfo_fromRef(v_ref_1707_, v___x_1708_);
                leanh::lean_dec(v_ref_1707_);
                v___x_1710_ = l_term___x3d_x3c_x3c___00__closed__1;
                v___x_1711_ = l_term___x3d_x3c_x3c___00__closed__2;
                leanh::lean_inc(v___x_1709_);
                v___x_1712_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1712_, 0, v___x_1709_);
                leanh::lean_ctor_set(v___x_1712_, 1, v___x_1711_);
                v___x_1713_ = l_Lean_Syntax_node3(
                    v___x_1709_,
                    v___x_1710_,
                    v___x_1705_,
                    v___x_1712_,
                    v___x_1706_,
                );
                v___x_1714_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1714_, 0, v___x_1713_);
                leanh::lean_ctor_set(v___x_1714_, 1, v_a_1688_);
                return v___x_1714_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1___boxed(
    mut v_x_1715_: *mut leanh::LeanObject,
    mut v_a_1716_: *mut leanh::LeanObject,
    mut v_a_1717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1718_ = l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(
        v_x_1715_, v_a_1716_, v_a_1717_,
    );
    leanh::lean_dec(v_a_1716_);
    return v_res_1718_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Basic(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Init_BinderNameHint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Basic(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_BinderNameHint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Control_Basic(builtin);
}