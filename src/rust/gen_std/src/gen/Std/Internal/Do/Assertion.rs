// Lean compiler output
// Module: Std.Internal.Do.Assertion
// Imports: Init.Internal.Order
use crate::r#gen::Init::Internal::Order::{
    initialize_Init_Internal_Order, runtime_initialize_Init_Internal_Order,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
pub static l_Lean_Order_term_u22a4___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Order_term_u22a4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Order_term_u22a4___closed__1_value: leanh::LeanStringObject<6> =
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
        m_data: [79, 114, 100, 101, 114, 0],
    };
static mut l_Lean_Order_term_u22a4___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Order_term_u22a4___closed__2_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 5,
        m_data: [116, 101, 114, 109, 226, 138, 164, 0],
    };
static mut l_Lean_Order_term_u22a4___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Order_term_u22a4___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Order_term_u22a4___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value)
                as *mut leanh::LeanObject,
            489434913524309295 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Order_term_u22a4___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__2_value)
                as *mut leanh::LeanObject,
            4896420126473035401 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term_u22a4___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Order_term_u22a4___closed__4_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 138, 164, 0],
    };
static mut l_Lean_Order_term_u22a4___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Order_term_u22a4___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term_u22a4___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Order_term_u22a4___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__3_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term_u22a4___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__6_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Order_term_u22a4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 111, 112, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0_value) as *mut leanh::LeanObject,4928918494582576983 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0_value) as *mut leanh::LeanObject,12247640180585144795 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 7,
        m_data: [116, 101, 114, 109, 95, 226, 138, 147, 95, 0],
    };
static mut l_Lean_Order_term___u2293___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Order_term___u2293___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Order_term___u2293___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value)
                as *mut leanh::LeanObject,
            489434913524309295 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Order_term___u2293___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__0_value)
                as *mut leanh::LeanObject,
            16606014227161981285 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2293___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__2_value: leanh::LeanStringObject<8> =
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
static mut l_Lean_Order_term___u2293___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__2_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2293___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__4_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 138, 147, 32, 0],
    };
static mut l_Lean_Order_term___u2293___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2293___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__6_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Order_term___u2293___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__6_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2293___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__8_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__7_value)
                as *mut leanh::LeanObject,
            (((71 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2293___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2293___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__10_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((70 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((70 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2293___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Order_term___u2293__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__1_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__2_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 101, 116, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4_value) as *mut leanh::LeanObject,2741269361911581766 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__6_value) as *mut leanh::LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4_value) as *mut leanh::LeanObject,12738217368988139970 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__10_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 7,
        m_data: [116, 101, 114, 109, 95, 226, 138, 148, 95, 0],
    };
static mut l_Lean_Order_term___u2294___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Order_term___u2294___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Order_term___u2294___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value)
                as *mut leanh::LeanObject,
            489434913524309295 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Order_term___u2294___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__0_value)
                as *mut leanh::LeanObject,
            15187416356175134241 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2294___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 138, 148, 32, 0],
    };
static mut l_Lean_Order_term___u2294___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2294___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__4_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__7_value)
                as *mut leanh::LeanObject,
            (((66 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2294___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2294___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__6_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((65 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((65 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u2294___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Order_term___u2294__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [106, 111, 105, 110, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0_value) as *mut leanh::LeanObject,5607412979871164673 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0_value) as *mut leanh::LeanObject,8142298027396223453 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__5_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Order_instPartialOrderProp__std: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Order_instCompleteLatticeProp__std: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_Do_term_u231c___u231d___closed__0_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Std_Internal_Do_term_u231c___u231d___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__1_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0],
};
static mut l_Std_Internal_Do_term_u231c___u231d___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__2_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [68, 111, 0],
};
static mut l_Std_Internal_Do_term_u231c___u231d___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__3_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 7,
    m_data: [116, 101, 114, 109, 226, 140, 156, 95, 226, 140, 157, 0],
};
static mut l_Std_Internal_Do_term_u231c___u231d___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__1_value)
            as *mut leanh::LeanObject,
        1742885236933170401 as *mut leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__2_value)
            as *mut leanh::LeanObject,
        1237304041707523237 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Internal_Do_term_u231c___u231d___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__3_value)
                as *mut leanh::LeanObject,
            10911529642982843935 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__5_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 140, 156, 0],
};
static mut l_Std_Internal_Do_term_u231c___u231d___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__7_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__9_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 140, 157, 0],
};
static mut l_Std_Internal_Do_term_u231c___u231d___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__10_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u231c___u231d___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__11_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u231c___u231d___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__12_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u231c___u231d___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__12_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_Do_term_u231c___u231d: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [65, 115, 115, 101, 114, 116, 105, 111, 110, 46, 111, 102, 80, 114, 111, 112, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [65, 115, 115, 101, 114, 116, 105, 111, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 102, 80, 114, 111, 112, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2_value) as *mut leanh::LeanObject,12974967848607075472 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3_value) as *mut leanh::LeanObject,1342330347679651256 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__1_value) as *mut leanh::LeanObject,1742885236933170401 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__2_value) as *mut leanh::LeanObject,1237304041707523237 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2_value) as *mut leanh::LeanObject,7306860446385387366 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3_value) as *mut leanh::LeanObject,15310354355589681094 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__7_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_421_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0;
    v___x_422_ = l_String_toRawSubstring_x27(v___x_421_);
    return v___x_422_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1(
    mut v_x_435_: *mut leanh::LeanObject,
    mut v_a_436_: *mut leanh::LeanObject,
    mut v_a_437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: u8 = 0;
    v___x_438_ = l_Lean_Order_term_u22a4___closed__3;
    v___x_439_ = l_Lean_Syntax_isOfKind(v_x_435_, v___x_438_);
    if v___x_439_ == 0 {
        let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_440_ = leanh::lean_box(1);
        v___x_441_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_441_, 0, v___x_440_);
        leanh::lean_ctor_set(v___x_441_, 1, v_a_437_);
        return v___x_441_;
    } else {
        let mut v_quotContext_442_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_443_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_445_: u8 = 0;
        let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_442_ = leanh::lean_ctor_get(v_a_436_, 1);
        v_currMacroScope_443_ = leanh::lean_ctor_get(v_a_436_, 2);
        v_ref_444_ = leanh::lean_ctor_get(v_a_436_, 5);
        v___x_445_ = 0;
        v___x_446_ = l_Lean_SourceInfo_fromRef(v_ref_444_, v___x_445_);
        v___x_447_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1_once), _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1);
        v___x_448_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__2;
        leanh::lean_inc(v_currMacroScope_443_);
        leanh::lean_inc(v_quotContext_442_);
        v___x_449_ = l_Lean_addMacroScope(v_quotContext_442_, v___x_448_, v_currMacroScope_443_);
        v___x_450_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__5;
        v___x_451_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_451_, 0, v___x_446_);
        leanh::lean_ctor_set(v___x_451_, 1, v___x_447_);
        leanh::lean_ctor_set(v___x_451_, 2, v___x_449_);
        leanh::lean_ctor_set(v___x_451_, 3, v___x_450_);
        v___x_452_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_452_, 0, v___x_451_);
        leanh::lean_ctor_set(v___x_452_, 1, v_a_437_);
        return v___x_452_;
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___boxed(
    mut v_x_453_: *mut leanh::LeanObject,
    mut v_a_454_: *mut leanh::LeanObject,
    mut v_a_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1(v_x_453_, v_a_454_, v_a_455_);
    leanh::lean_dec_ref(v_a_454_);
    return v_res_456_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1(
    mut v_x_460_: *mut leanh::LeanObject,
    mut v_a_461_: *mut leanh::LeanObject,
    mut v_a_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: u8 = 0;
    v___x_463_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1;
    leanh::lean_inc(v_x_460_);
    v___x_464_ = l_Lean_Syntax_isOfKind(v_x_460_, v___x_463_);
    if v___x_464_ == 0 {
        let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_460_);
        v___x_465_ = leanh::lean_box(0);
        v___x_466_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_466_, 0, v___x_465_);
        leanh::lean_ctor_set(v___x_466_, 1, v_a_462_);
        return v___x_466_;
    } else {
        let mut v_ref_467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_468_: u8 = 0;
        let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_467_ = l_Lean_replaceRef(v_x_460_, v_a_461_);
        leanh::lean_dec(v_x_460_);
        v___x_468_ = 0;
        v___x_469_ = l_Lean_SourceInfo_fromRef(v_ref_467_, v___x_468_);
        leanh::lean_dec(v_ref_467_);
        v___x_470_ = l_Lean_Order_term_u22a4___closed__3;
        v___x_471_ = l_Lean_Order_term_u22a4___closed__4;
        leanh::lean_inc(v___x_469_);
        v___x_472_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_472_, 0, v___x_469_);
        leanh::lean_ctor_set(v___x_472_, 1, v___x_471_);
        v___x_473_ = l_Lean_Syntax_node1(v___x_469_, v___x_470_, v___x_472_);
        v___x_474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_474_, 0, v___x_473_);
        leanh::lean_ctor_set(v___x_474_, 1, v_a_462_);
        return v___x_474_;
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___boxed(
    mut v_x_475_: *mut leanh::LeanObject,
    mut v_a_476_: *mut leanh::LeanObject,
    mut v_a_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ =
        l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1(
            v_x_475_, v_a_476_, v_a_477_,
        );
    leanh::lean_dec(v_a_476_);
    return v_res_478_;
}
pub unsafe fn _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4;
    v___x_515_ = l_String_toRawSubstring_x27(v___x_514_);
    return v___x_515_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1(
    mut v_x_531_: *mut leanh::LeanObject,
    mut v_a_532_: *mut leanh::LeanObject,
    mut v_a_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    v___x_534_ = l_Lean_Order_term___u2293___00__closed__1;
    leanh::lean_inc(v_x_531_);
    v___x_535_ = l_Lean_Syntax_isOfKind(v_x_531_, v___x_534_);
    if v___x_535_ == 0 {
        let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_531_);
        v___x_536_ = leanh::lean_box(1);
        v___x_537_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_537_, 0, v___x_536_);
        leanh::lean_ctor_set(v___x_537_, 1, v_a_533_);
        return v___x_537_;
    } else {
        let mut v_quotContext_538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_545_: u8 = 0;
        let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_538_ = leanh::lean_ctor_get(v_a_532_, 1);
        v_currMacroScope_539_ = leanh::lean_ctor_get(v_a_532_, 2);
        v_ref_540_ = leanh::lean_ctor_get(v_a_532_, 5);
        v___x_541_ = leanh::lean_unsigned_to_nat(0);
        v___x_542_ = l_Lean_Syntax_getArg(v_x_531_, v___x_541_);
        v___x_543_ = leanh::lean_unsigned_to_nat(2);
        v___x_544_ = l_Lean_Syntax_getArg(v_x_531_, v___x_543_);
        leanh::lean_dec(v_x_531_);
        v___x_545_ = 0;
        v___x_546_ = l_Lean_SourceInfo_fromRef(v_ref_540_, v___x_545_);
        v___x_547_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
        v___x_548_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5), core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5_once), _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5);
        v___x_549_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__6;
        leanh::lean_inc(v_currMacroScope_539_);
        leanh::lean_inc(v_quotContext_538_);
        v___x_550_ = l_Lean_addMacroScope(v_quotContext_538_, v___x_549_, v_currMacroScope_539_);
        v___x_551_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__9;
        leanh::lean_inc_n(v___x_546_, 2);
        v___x_552_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_552_, 0, v___x_546_);
        leanh::lean_ctor_set(v___x_552_, 1, v___x_548_);
        leanh::lean_ctor_set(v___x_552_, 2, v___x_550_);
        leanh::lean_ctor_set(v___x_552_, 3, v___x_551_);
        v___x_553_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11;
        v___x_554_ = l_Lean_Syntax_node2(v___x_546_, v___x_553_, v___x_542_, v___x_544_);
        v___x_555_ = l_Lean_Syntax_node2(v___x_546_, v___x_547_, v___x_552_, v___x_554_);
        v___x_556_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_556_, 0, v___x_555_);
        leanh::lean_ctor_set(v___x_556_, 1, v_a_533_);
        return v___x_556_;
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___boxed(
    mut v_x_557_: *mut leanh::LeanObject,
    mut v_a_558_: *mut leanh::LeanObject,
    mut v_a_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1(v_x_557_, v_a_558_, v_a_559_);
    leanh::lean_dec_ref(v_a_558_);
    return v_res_560_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__meet__1(
    mut v_x_561_: *mut leanh::LeanObject,
    mut v_a_562_: *mut leanh::LeanObject,
    mut v_a_563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u8 = 0;
    v___x_564_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
    leanh::lean_inc(v_x_561_);
    v___x_565_ = l_Lean_Syntax_isOfKind(v_x_561_, v___x_564_);
    if v___x_565_ == 0 {
        let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_561_);
        v___x_566_ = leanh::lean_box(0);
        v___x_567_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_567_, 0, v___x_566_);
        leanh::lean_ctor_set(v___x_567_, 1, v_a_563_);
        return v___x_567_;
    } else {
        let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_571_: u8 = 0;
        v___x_568_ = leanh::lean_unsigned_to_nat(0);
        v___x_569_ = l_Lean_Syntax_getArg(v_x_561_, v___x_568_);
        v___x_570_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1;
        leanh::lean_inc(v___x_569_);
        v___x_571_ = l_Lean_Syntax_isOfKind(v___x_569_, v___x_570_);
        if v___x_571_ == 0 {
            let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_569_);
            leanh::lean_dec(v_x_561_);
            v___x_572_ = leanh::lean_box(0);
            v___x_573_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_573_, 0, v___x_572_);
            leanh::lean_ctor_set(v___x_573_, 1, v_a_563_);
            return v___x_573_;
        } else {
            let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_577_: u8 = 0;
            v___x_574_ = leanh::lean_unsigned_to_nat(1);
            v___x_575_ = l_Lean_Syntax_getArg(v_x_561_, v___x_574_);
            leanh::lean_dec(v_x_561_);
            v___x_576_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_575_);
            v___x_577_ = l_Lean_Syntax_matchesNull(v___x_575_, v___x_576_);
            if v___x_577_ == 0 {
                let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_575_);
                leanh::lean_dec(v___x_569_);
                v___x_578_ = leanh::lean_box(0);
                v___x_579_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_579_, 0, v___x_578_);
                leanh::lean_ctor_set(v___x_579_, 1, v_a_563_);
                return v___x_579_;
            } else {
                let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_582_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_583_: u8 = 0;
                let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_580_ = l_Lean_Syntax_getArg(v___x_575_, v___x_568_);
                v___x_581_ = l_Lean_Syntax_getArg(v___x_575_, v___x_574_);
                leanh::lean_dec(v___x_575_);
                v_ref_582_ = l_Lean_replaceRef(v___x_569_, v_a_562_);
                leanh::lean_dec(v___x_569_);
                v___x_583_ = 0;
                v___x_584_ = l_Lean_SourceInfo_fromRef(v_ref_582_, v___x_583_);
                leanh::lean_dec(v_ref_582_);
                v___x_585_ = l_Lean_Order_term___u2293___00__closed__1;
                v___x_586_ = l_Lean_Order_term___u2293___00__closed__4;
                leanh::lean_inc(v___x_584_);
                v___x_587_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_587_, 0, v___x_584_);
                leanh::lean_ctor_set(v___x_587_, 1, v___x_586_);
                v___x_588_ =
                    l_Lean_Syntax_node3(v___x_584_, v___x_585_, v___x_580_, v___x_587_, v___x_581_);
                v___x_589_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_589_, 0, v___x_588_);
                leanh::lean_ctor_set(v___x_589_, 1, v_a_563_);
                return v___x_589_;
            }
        }
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__meet__1___boxed(
    mut v_x_590_: *mut leanh::LeanObject,
    mut v_a_591_: *mut leanh::LeanObject,
    mut v_a_592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_593_ =
        l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__meet__1(
            v_x_590_, v_a_591_, v_a_592_,
        );
    leanh::lean_dec(v_a_591_);
    return v_res_593_;
}
pub unsafe fn _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_615_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0;
    v___x_616_ = l_String_toRawSubstring_x27(v___x_615_);
    return v___x_616_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1(
    mut v_x_629_: *mut leanh::LeanObject,
    mut v_a_630_: *mut leanh::LeanObject,
    mut v_a_631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: u8 = 0;
    v___x_632_ = l_Lean_Order_term___u2294___00__closed__1;
    leanh::lean_inc(v_x_629_);
    v___x_633_ = l_Lean_Syntax_isOfKind(v_x_629_, v___x_632_);
    if v___x_633_ == 0 {
        let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_629_);
        v___x_634_ = leanh::lean_box(1);
        v___x_635_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_635_, 0, v___x_634_);
        leanh::lean_ctor_set(v___x_635_, 1, v_a_631_);
        return v___x_635_;
    } else {
        let mut v_quotContext_636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_637_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_643_: u8 = 0;
        let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_636_ = leanh::lean_ctor_get(v_a_630_, 1);
        v_currMacroScope_637_ = leanh::lean_ctor_get(v_a_630_, 2);
        v_ref_638_ = leanh::lean_ctor_get(v_a_630_, 5);
        v___x_639_ = leanh::lean_unsigned_to_nat(0);
        v___x_640_ = l_Lean_Syntax_getArg(v_x_629_, v___x_639_);
        v___x_641_ = leanh::lean_unsigned_to_nat(2);
        v___x_642_ = l_Lean_Syntax_getArg(v_x_629_, v___x_641_);
        leanh::lean_dec(v_x_629_);
        v___x_643_ = 0;
        v___x_644_ = l_Lean_SourceInfo_fromRef(v_ref_638_, v___x_643_);
        v___x_645_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
        v___x_646_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1), core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1_once), _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1);
        v___x_647_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__2;
        leanh::lean_inc(v_currMacroScope_637_);
        leanh::lean_inc(v_quotContext_636_);
        v___x_648_ = l_Lean_addMacroScope(v_quotContext_636_, v___x_647_, v_currMacroScope_637_);
        v___x_649_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__5;
        leanh::lean_inc_n(v___x_644_, 2);
        v___x_650_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_650_, 0, v___x_644_);
        leanh::lean_ctor_set(v___x_650_, 1, v___x_646_);
        leanh::lean_ctor_set(v___x_650_, 2, v___x_648_);
        leanh::lean_ctor_set(v___x_650_, 3, v___x_649_);
        v___x_651_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11;
        v___x_652_ = l_Lean_Syntax_node2(v___x_644_, v___x_651_, v___x_640_, v___x_642_);
        v___x_653_ = l_Lean_Syntax_node2(v___x_644_, v___x_645_, v___x_650_, v___x_652_);
        v___x_654_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_654_, 0, v___x_653_);
        leanh::lean_ctor_set(v___x_654_, 1, v_a_631_);
        return v___x_654_;
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___boxed(
    mut v_x_655_: *mut leanh::LeanObject,
    mut v_a_656_: *mut leanh::LeanObject,
    mut v_a_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_658_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1(v_x_655_, v_a_656_, v_a_657_);
    leanh::lean_dec_ref(v_a_656_);
    return v_res_658_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__join__1(
    mut v_x_659_: *mut leanh::LeanObject,
    mut v_a_660_: *mut leanh::LeanObject,
    mut v_a_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: u8 = 0;
    v___x_662_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
    leanh::lean_inc(v_x_659_);
    v___x_663_ = l_Lean_Syntax_isOfKind(v_x_659_, v___x_662_);
    if v___x_663_ == 0 {
        let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_659_);
        v___x_664_ = leanh::lean_box(0);
        v___x_665_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_665_, 0, v___x_664_);
        leanh::lean_ctor_set(v___x_665_, 1, v_a_661_);
        return v___x_665_;
    } else {
        let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_669_: u8 = 0;
        v___x_666_ = leanh::lean_unsigned_to_nat(0);
        v___x_667_ = l_Lean_Syntax_getArg(v_x_659_, v___x_666_);
        v___x_668_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1;
        leanh::lean_inc(v___x_667_);
        v___x_669_ = l_Lean_Syntax_isOfKind(v___x_667_, v___x_668_);
        if v___x_669_ == 0 {
            let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_667_);
            leanh::lean_dec(v_x_659_);
            v___x_670_ = leanh::lean_box(0);
            v___x_671_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_671_, 0, v___x_670_);
            leanh::lean_ctor_set(v___x_671_, 1, v_a_661_);
            return v___x_671_;
        } else {
            let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_675_: u8 = 0;
            v___x_672_ = leanh::lean_unsigned_to_nat(1);
            v___x_673_ = l_Lean_Syntax_getArg(v_x_659_, v___x_672_);
            leanh::lean_dec(v_x_659_);
            v___x_674_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_673_);
            v___x_675_ = l_Lean_Syntax_matchesNull(v___x_673_, v___x_674_);
            if v___x_675_ == 0 {
                let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_673_);
                leanh::lean_dec(v___x_667_);
                v___x_676_ = leanh::lean_box(0);
                v___x_677_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_677_, 0, v___x_676_);
                leanh::lean_ctor_set(v___x_677_, 1, v_a_661_);
                return v___x_677_;
            } else {
                let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_680_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_681_: u8 = 0;
                let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_678_ = l_Lean_Syntax_getArg(v___x_673_, v___x_666_);
                v___x_679_ = l_Lean_Syntax_getArg(v___x_673_, v___x_672_);
                leanh::lean_dec(v___x_673_);
                v_ref_680_ = l_Lean_replaceRef(v___x_667_, v_a_660_);
                leanh::lean_dec(v___x_667_);
                v___x_681_ = 0;
                v___x_682_ = l_Lean_SourceInfo_fromRef(v_ref_680_, v___x_681_);
                leanh::lean_dec(v_ref_680_);
                v___x_683_ = l_Lean_Order_term___u2294___00__closed__1;
                v___x_684_ = l_Lean_Order_term___u2294___00__closed__2;
                leanh::lean_inc(v___x_682_);
                v___x_685_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_685_, 0, v___x_682_);
                leanh::lean_ctor_set(v___x_685_, 1, v___x_684_);
                v___x_686_ =
                    l_Lean_Syntax_node3(v___x_682_, v___x_683_, v___x_678_, v___x_685_, v___x_679_);
                v___x_687_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_687_, 0, v___x_686_);
                leanh::lean_ctor_set(v___x_687_, 1, v_a_661_);
                return v___x_687_;
            }
        }
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__join__1___boxed(
    mut v_x_688_: *mut leanh::LeanObject,
    mut v_a_689_: *mut leanh::LeanObject,
    mut v_a_690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_691_ =
        l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__join__1(
            v_x_688_, v_a_689_, v_a_690_,
        );
    leanh::lean_dec(v_a_689_);
    return v_res_691_;
}
pub unsafe fn _init_l_Lean_Order_instPartialOrderProp__std() -> *mut leanh::LeanObject {
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_692_ = leanh::lean_box(0);
    return v___x_692_;
}
pub unsafe fn _init_l_Lean_Order_instCompleteLatticeProp__std() -> *mut leanh::LeanObject {
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ = leanh::lean_box(0);
    return v___x_693_;
}
pub unsafe fn l_Std_Internal_Do_instCCPOOfAssertion___redArg(
    mut v_inst_694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    return v_inst_694_;
}
pub unsafe fn l_Std_Internal_Do_instCCPOOfAssertion(
    mut v_EPred_695_: *mut leanh::LeanObject,
    mut v_inst_696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    return v_inst_696_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_729_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__0;
    v___x_730_ = l_String_toRawSubstring_x27(v___x_729_);
    return v___x_730_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1(
    mut v_x_748_: *mut leanh::LeanObject,
    mut v_a_749_: *mut leanh::LeanObject,
    mut v_a_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: u8 = 0;
    v___x_751_ = l_Std_Internal_Do_term_u231c___u231d___closed__4;
    leanh::lean_inc(v_x_748_);
    v___x_752_ = l_Lean_Syntax_isOfKind(v_x_748_, v___x_751_);
    if v___x_752_ == 0 {
        let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_748_);
        v___x_753_ = leanh::lean_box(1);
        v___x_754_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_754_, 0, v___x_753_);
        leanh::lean_ctor_set(v___x_754_, 1, v_a_750_);
        return v___x_754_;
    } else {
        let mut v_quotContext_755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_760_: u8 = 0;
        let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_755_ = leanh::lean_ctor_get(v_a_749_, 1);
        v_currMacroScope_756_ = leanh::lean_ctor_get(v_a_749_, 2);
        v_ref_757_ = leanh::lean_ctor_get(v_a_749_, 5);
        v___x_758_ = leanh::lean_unsigned_to_nat(1);
        v___x_759_ = l_Lean_Syntax_getArg(v_x_748_, v___x_758_);
        leanh::lean_dec(v_x_748_);
        v___x_760_ = 0;
        v___x_761_ = l_Lean_SourceInfo_fromRef(v_ref_757_, v___x_760_);
        v___x_762_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
        v___x_763_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1);
        v___x_764_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4;
        leanh::lean_inc(v_currMacroScope_756_);
        leanh::lean_inc(v_quotContext_755_);
        v___x_765_ = l_Lean_addMacroScope(v_quotContext_755_, v___x_764_, v_currMacroScope_756_);
        v___x_766_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__7;
        leanh::lean_inc_n(v___x_761_, 2);
        v___x_767_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_767_, 0, v___x_761_);
        leanh::lean_ctor_set(v___x_767_, 1, v___x_763_);
        leanh::lean_ctor_set(v___x_767_, 2, v___x_765_);
        leanh::lean_ctor_set(v___x_767_, 3, v___x_766_);
        v___x_768_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11;
        v___x_769_ = l_Lean_Syntax_node1(v___x_761_, v___x_768_, v___x_759_);
        v___x_770_ = l_Lean_Syntax_node2(v___x_761_, v___x_762_, v___x_767_, v___x_769_);
        v___x_771_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_771_, 0, v___x_770_);
        leanh::lean_ctor_set(v___x_771_, 1, v_a_750_);
        return v___x_771_;
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___boxed(
    mut v_x_772_: *mut leanh::LeanObject,
    mut v_a_773_: *mut leanh::LeanObject,
    mut v_a_774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1(v_x_772_, v_a_773_, v_a_774_);
    leanh::lean_dec_ref(v_a_773_);
    return v_res_775_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______unexpand__Std__Internal__Do__Assertion__ofProp__1(
    mut v_x_776_: *mut leanh::LeanObject,
    mut v_a_777_: *mut leanh::LeanObject,
    mut v_a_778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: u8 = 0;
    v___x_779_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
    leanh::lean_inc(v_x_776_);
    v___x_780_ = l_Lean_Syntax_isOfKind(v_x_776_, v___x_779_);
    if v___x_780_ == 0 {
        let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_776_);
        v___x_781_ = leanh::lean_box(0);
        v___x_782_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_782_, 0, v___x_781_);
        leanh::lean_ctor_set(v___x_782_, 1, v_a_778_);
        return v___x_782_;
    } else {
        let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_786_: u8 = 0;
        v___x_783_ = leanh::lean_unsigned_to_nat(0);
        v___x_784_ = l_Lean_Syntax_getArg(v_x_776_, v___x_783_);
        v___x_785_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1;
        leanh::lean_inc(v___x_784_);
        v___x_786_ = l_Lean_Syntax_isOfKind(v___x_784_, v___x_785_);
        if v___x_786_ == 0 {
            let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_784_);
            leanh::lean_dec(v_x_776_);
            v___x_787_ = leanh::lean_box(0);
            v___x_788_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_788_, 0, v___x_787_);
            leanh::lean_ctor_set(v___x_788_, 1, v_a_778_);
            return v___x_788_;
        } else {
            let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_791_: u8 = 0;
            v___x_789_ = leanh::lean_unsigned_to_nat(1);
            v___x_790_ = l_Lean_Syntax_getArg(v_x_776_, v___x_789_);
            leanh::lean_dec(v_x_776_);
            leanh::lean_inc(v___x_790_);
            v___x_791_ = l_Lean_Syntax_matchesNull(v___x_790_, v___x_789_);
            if v___x_791_ == 0 {
                let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_790_);
                leanh::lean_dec(v___x_784_);
                v___x_792_ = leanh::lean_box(0);
                v___x_793_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_793_, 0, v___x_792_);
                leanh::lean_ctor_set(v___x_793_, 1, v_a_778_);
                return v___x_793_;
            } else {
                let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_795_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_796_: u8 = 0;
                let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_794_ = l_Lean_Syntax_getArg(v___x_790_, v___x_783_);
                leanh::lean_dec(v___x_790_);
                v_ref_795_ = l_Lean_replaceRef(v___x_784_, v_a_777_);
                leanh::lean_dec(v___x_784_);
                v___x_796_ = 0;
                v___x_797_ = l_Lean_SourceInfo_fromRef(v_ref_795_, v___x_796_);
                leanh::lean_dec(v_ref_795_);
                v___x_798_ = l_Std_Internal_Do_term_u231c___u231d___closed__4;
                v___x_799_ = l_Std_Internal_Do_term_u231c___u231d___closed__5;
                leanh::lean_inc_n(v___x_797_, 2);
                v___x_800_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_800_, 0, v___x_797_);
                leanh::lean_ctor_set(v___x_800_, 1, v___x_799_);
                v___x_801_ = l_Std_Internal_Do_term_u231c___u231d___closed__9;
                v___x_802_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_802_, 0, v___x_797_);
                leanh::lean_ctor_set(v___x_802_, 1, v___x_801_);
                v___x_803_ =
                    l_Lean_Syntax_node3(v___x_797_, v___x_798_, v___x_800_, v___x_794_, v___x_802_);
                v___x_804_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_804_, 0, v___x_803_);
                leanh::lean_ctor_set(v___x_804_, 1, v_a_778_);
                return v___x_804_;
            }
        }
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______unexpand__Std__Internal__Do__Assertion__ofProp__1___boxed(
    mut v_x_805_: *mut leanh::LeanObject,
    mut v_a_806_: *mut leanh::LeanObject,
    mut v_a_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______unexpand__Std__Internal__Do__Assertion__ofProp__1(v_x_805_, v_a_806_, v_a_807_);
    leanh::lean_dec(v_a_806_);
    return v_res_808_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_Assertion(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Internal_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Order_instPartialOrderProp__std = _init_l_Lean_Order_instPartialOrderProp__std();
    leanh::lean_mark_persistent(l_Lean_Order_instPartialOrderProp__std);
    l_Lean_Order_instCompleteLatticeProp__std = _init_l_Lean_Order_instCompleteLatticeProp__std();
    leanh::lean_mark_persistent(l_Lean_Order_instCompleteLatticeProp__std);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_Assertion(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_Do_Assertion(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Internal_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_Assertion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_Assertion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_Assertion(builtin);
}