// Lean compiler output
// Module: Init.Data.ToString.Macro
// Imports: Init.Meta Init.Notation
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_expandInterpolatedStr;
use crate::r#gen::Init::Meta::{initialize_Init_Meta, runtime_initialize_Init_Meta};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_addMacroScope,
    l_String_toRawSubstring_x27,
};
pub static l_termS_x21___00__closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 83, 33, 95, 0],
    };
static mut l_termS_x21___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__0_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_termS_x21___00__closed__0_value) as *mut leanh::LeanObject,
            11081549158230622750 as *mut leanh::LeanObject,
        ],
    };
static mut l_termS_x21___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__1_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__2_value: leanh::LeanStringObject<8> =
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
static mut l_termS_x21___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__2_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_termS_x21___00__closed__2_value) as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_termS_x21___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__3_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__4_value: leanh::LeanStringObject<3> =
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
        m_data: [115, 33, 0],
    };
static mut l_termS_x21___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__4_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_termS_x21___00__closed__4_value) as *mut leanh::LeanObject
        ],
    };
static mut l_termS_x21___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__5_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__6_value: leanh::LeanStringObject<16> =
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
            105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
        ],
    };
static mut l_termS_x21___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__6_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_termS_x21___00__closed__6_value) as *mut leanh::LeanObject,
            18163029821153688220 as *mut leanh::LeanObject,
        ],
    };
static mut l_termS_x21___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__7_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_termS_x21___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__8_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_termS_x21___00__closed__8_value) as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_termS_x21___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__9_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_termS_x21___00__closed__9_value) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_termS_x21___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__10_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__11_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_termS_x21___00__closed__7_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_termS_x21___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_termS_x21___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__11_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_termS_x21___00__closed__3_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_termS_x21___00__closed__5_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_termS_x21___00__closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_termS_x21___00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__12_value) as *mut leanh::LeanObject;
pub static l_termS_x21___00__closed__13_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_termS_x21___00__closed__1_value) as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_termS_x21___00__closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_termS_x21___00__closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__13_value) as *mut leanh::LeanObject;
pub static mut l_termS_x21__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_termS_x21___00__closed__13_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 105, 110, 103, 0]};
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0_value) as *mut leanh::LeanObject,3136308715950998022 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__3_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2_value) as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__4_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__5_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__5_value) as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__6_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 83, 116, 114, 105, 110, 103, 0]};
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7_value) as *mut leanh::LeanObject,16359081359533231919 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__9_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__10_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 111, 83, 116, 114, 105, 110, 103, 0]};
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__10_value
) as *mut leanh::LeanObject;
static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__10_value) as *mut leanh::LeanObject,12150634900968360478 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7_value) as *mut leanh::LeanObject,7720788540864844494 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__12_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__12_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__13_value
) as *mut leanh::LeanObject;
pub unsafe fn _init_l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_140_ = l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0;
    v___x_141_ = l_String_toRawSubstring_x27(v___x_140_);
    return v___x_141_;
}
pub unsafe fn _init_l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_156_ = l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7;
    v___x_157_ = l_String_toRawSubstring_x27(v___x_156_);
    return v___x_157_;
}
pub unsafe fn l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1(
    mut v_x_170_: *mut leanh::LeanObject,
    mut v_a_171_: *mut leanh::LeanObject,
    mut v_a_172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: u8 = 0;
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interpStr_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: u8 = 0;
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_199_: u8 = 0;
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_203_: u8 = 0;
    let mut v_a_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_208_: u8 = 0;
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_173_ = l_termS_x21___00__closed__1;
                leanh::lean_inc(v_x_170_);
                v___x_174_ = l_Lean_Syntax_isOfKind(v_x_170_, v___x_173_);
                if v___x_174_ == 0 {
                    leanh::lean_dec(v_x_170_);
                    v___x_175_ = leanh::lean_box(1);
                    v___x_176_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_176_, 0, v___x_175_);
                    leanh::lean_ctor_set(v___x_176_, 1, v_a_172_);
                    return v___x_176_;
                } else {
                    v_quotContext_177_ = leanh::lean_ctor_get(v_a_171_, 1);
                    v_currMacroScope_178_ = leanh::lean_ctor_get(v_a_171_, 2);
                    v_ref_179_ = leanh::lean_ctor_get(v_a_171_, 5);
                    v___x_180_ = leanh::lean_unsigned_to_nat(1);
                    v_interpStr_181_ = l_Lean_Syntax_getArg(v_x_170_, v___x_180_);
                    leanh::lean_dec(v_x_170_);
                    v___x_182_ = 0;
                    v___x_183_ = l_Lean_SourceInfo_fromRef(v_ref_179_, v___x_182_);
                    v___x_184_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1_once), _init_l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1);
                    v___x_185_ = l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2;
                    leanh::lean_inc_n(v_currMacroScope_178_, 2);
                    leanh::lean_inc_n(v_quotContext_177_, 2);
                    v___x_186_ =
                        l_Lean_addMacroScope(v_quotContext_177_, v___x_185_, v_currMacroScope_178_);
                    v___x_187_ = l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__6;
                    leanh::lean_inc(v___x_183_);
                    v___x_188_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_188_, 0, v___x_183_);
                    leanh::lean_ctor_set(v___x_188_, 1, v___x_184_);
                    leanh::lean_ctor_set(v___x_188_, 2, v___x_186_);
                    leanh::lean_ctor_set(v___x_188_, 3, v___x_187_);
                    v___x_189_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8), core::ptr::addr_of_mut!(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8_once), _init_l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8);
                    v___x_190_ = l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__9;
                    v___x_191_ =
                        l_Lean_addMacroScope(v_quotContext_177_, v___x_190_, v_currMacroScope_178_);
                    v___x_192_ = l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__13;
                    v___x_193_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_193_, 0, v___x_183_);
                    leanh::lean_ctor_set(v___x_193_, 1, v___x_189_);
                    leanh::lean_ctor_set(v___x_193_, 2, v___x_191_);
                    leanh::lean_ctor_set(v___x_193_, 3, v___x_192_);
                    leanh::lean_inc_ref(v___x_193_);
                    v___x_194_ = l_Lean_TSyntax_expandInterpolatedStr(
                        v_interpStr_181_,
                        v___x_188_,
                        v___x_193_,
                        v___x_193_,
                        v_a_171_,
                        v_a_172_,
                    );
                    leanh::lean_dec(v_interpStr_181_);
                    if leanh::lean_obj_tag(v___x_194_) == 0 {
                        v_a_195_ = leanh::lean_ctor_get(v___x_194_, 0);
                        v_a_196_ = leanh::lean_ctor_get(v___x_194_, 1);
                        v_isSharedCheck_203_ = (!leanh::lean_is_exclusive(v___x_194_)) as u8;
                        if v_isSharedCheck_203_ == 0 {
                            v___x_198_ = v___x_194_;
                            v_isShared_199_ = v_isSharedCheck_203_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_196_);
                            leanh::lean_inc(v_a_195_);
                            leanh::lean_dec(v___x_194_);
                            v___x_198_ = leanh::lean_box(0);
                            v_isShared_199_ = v_isSharedCheck_203_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_204_ = leanh::lean_ctor_get(v___x_194_, 0);
                        v_a_205_ = leanh::lean_ctor_get(v___x_194_, 1);
                        v_isSharedCheck_212_ = (!leanh::lean_is_exclusive(v___x_194_)) as u8;
                        if v_isSharedCheck_212_ == 0 {
                            v___x_207_ = v___x_194_;
                            v_isShared_208_ = v_isSharedCheck_212_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_205_);
                            leanh::lean_inc(v_a_204_);
                            leanh::lean_dec(v___x_194_);
                            v___x_207_ = leanh::lean_box(0);
                            v_isShared_208_ = v_isSharedCheck_212_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_199_ == 0 {
                    v___x_201_ = v___x_198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_202_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_202_, 1, v_a_196_);
                    v___x_201_ = v_reuseFailAlloc_202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_201_;
            }
            3 => {
                if v_isShared_208_ == 0 {
                    v___x_210_ = v___x_207_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_211_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_211_, 1, v_a_205_);
                    v___x_210_ = v_reuseFailAlloc_211_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___boxed(
    mut v_x_213_: *mut leanh::LeanObject,
    mut v_a_214_: *mut leanh::LeanObject,
    mut v_a_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ = l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1(
        v_x_213_, v_a_214_, v_a_215_,
    );
    leanh::lean_dec_ref(v_a_214_);
    return v_res_216_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ToString_Macro(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_ToString_Macro(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_ToString_Macro(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_ToString_Macro(builtin);
}