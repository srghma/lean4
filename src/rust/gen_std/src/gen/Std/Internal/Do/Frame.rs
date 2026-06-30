// Lean compiler output
// Module: Std.Internal.Do.Frame
// Imports: Std.Internal.Do.Assertion
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Internal::Do::Assertion::{
    initialize_Std_Internal_Do_Assertion, runtime_initialize_Std_Internal_Do_Assertion,
};
pub static l_Lean_Order_term___u21e8___00__closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Order_term___u21e8___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__1_value: leanh::LeanStringObject<6> =
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
static mut l_Lean_Order_term___u21e8___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__2_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 226, 135, 168, 95, 0],
    };
static mut l_Lean_Order_term___u21e8___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Order_term___u21e8___00__closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Order_term___u21e8___00__closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__1_value)
                as *mut leanh::LeanObject,
            489434913524309295 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Order_term___u21e8___00__closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__2_value)
                as *mut leanh::LeanObject,
            12366595419020007340 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u21e8___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__4_value: leanh::LeanStringObject<8> =
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
static mut l_Lean_Order_term___u21e8___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__4_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u21e8___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__6_value: leanh::LeanStringObject<6> =
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
        m_data: [32, 226, 135, 168, 32, 0],
    };
static mut l_Lean_Order_term___u21e8___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__7_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u21e8___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Order_term___u21e8___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__8_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u21e8___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__9_value)
                as *mut leanh::LeanObject,
            (((60 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u21e8___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u21e8___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order_term___u21e8___00__closed__12_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__3_value)
                as *mut leanh::LeanObject,
            (((60 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((61 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Order_term___u21e8___00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Order_term___u21e8__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__1_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__2_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 105, 109, 112, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4_value) as *mut leanh::LeanObject,719708620230712625 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__6_value) as *mut leanh::LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order_term___u21e8___00__closed__1_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4_value) as *mut leanh::LeanObject,10100903285623889325 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__7_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__10_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_160_ = l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__4;
    v___x_161_ = l_String_toRawSubstring_x27(v___x_160_);
    return v___x_161_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1(
    mut v_x_177_: *mut leanh::LeanObject,
    mut v_a_178_: *mut leanh::LeanObject,
    mut v_a_179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: u8 = 0;
    v___x_180_ = l_Lean_Order_term___u21e8___00__closed__3;
    leanh::lean_inc(v_x_177_);
    v___x_181_ = l_Lean_Syntax_isOfKind(v_x_177_, v___x_180_);
    if v___x_181_ == 0 {
        let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_177_);
        v___x_182_ = leanh::lean_box(1);
        v___x_183_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_183_, 0, v___x_182_);
        leanh::lean_ctor_set(v___x_183_, 1, v_a_179_);
        return v___x_183_;
    } else {
        let mut v_quotContext_184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_191_: u8 = 0;
        let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_184_ = leanh::lean_ctor_get(v_a_178_, 1);
        v_currMacroScope_185_ = leanh::lean_ctor_get(v_a_178_, 2);
        v_ref_186_ = leanh::lean_ctor_get(v_a_178_, 5);
        v___x_187_ = leanh::lean_unsigned_to_nat(0);
        v___x_188_ = l_Lean_Syntax_getArg(v_x_177_, v___x_187_);
        v___x_189_ = leanh::lean_unsigned_to_nat(2);
        v___x_190_ = l_Lean_Syntax_getArg(v_x_177_, v___x_189_);
        leanh::lean_dec(v_x_177_);
        v___x_191_ = 0;
        v___x_192_ = l_Lean_SourceInfo_fromRef(v_ref_186_, v___x_191_);
        v___x_193_ = l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3;
        v___x_194_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5), core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5_once), _init_l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__5);
        v___x_195_ = l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__6;
        leanh::lean_inc(v_currMacroScope_185_);
        leanh::lean_inc(v_quotContext_184_);
        v___x_196_ = l_Lean_addMacroScope(v_quotContext_184_, v___x_195_, v_currMacroScope_185_);
        v___x_197_ = l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__9;
        leanh::lean_inc_n(v___x_192_, 2);
        v___x_198_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_198_, 0, v___x_192_);
        leanh::lean_ctor_set(v___x_198_, 1, v___x_194_);
        leanh::lean_ctor_set(v___x_198_, 2, v___x_196_);
        leanh::lean_ctor_set(v___x_198_, 3, v___x_197_);
        v___x_199_ = l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__11;
        v___x_200_ = l_Lean_Syntax_node2(v___x_192_, v___x_199_, v___x_188_, v___x_190_);
        v___x_201_ = l_Lean_Syntax_node2(v___x_192_, v___x_193_, v___x_198_, v___x_200_);
        v___x_202_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_202_, 0, v___x_201_);
        leanh::lean_ctor_set(v___x_202_, 1, v_a_179_);
        return v___x_202_;
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___boxed(
    mut v_x_203_: *mut leanh::LeanObject,
    mut v_a_204_: *mut leanh::LeanObject,
    mut v_a_205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_206_ = l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1(v_x_203_, v_a_204_, v_a_205_);
    leanh::lean_dec_ref(v_a_204_);
    return v_res_206_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1(
    mut v_x_210_: *mut leanh::LeanObject,
    mut v_a_211_: *mut leanh::LeanObject,
    mut v_a_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: u8 = 0;
    v___x_213_ = l_Lean_Order___aux__Std__Internal__Do__Frame______macroRules__Lean__Order__term___u21e8____1___closed__3;
    leanh::lean_inc(v_x_210_);
    v___x_214_ = l_Lean_Syntax_isOfKind(v_x_210_, v___x_213_);
    if v___x_214_ == 0 {
        let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_210_);
        v___x_215_ = leanh::lean_box(0);
        v___x_216_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_216_, 0, v___x_215_);
        leanh::lean_ctor_set(v___x_216_, 1, v_a_212_);
        return v___x_216_;
    } else {
        let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_220_: u8 = 0;
        v___x_217_ = leanh::lean_unsigned_to_nat(0);
        v___x_218_ = l_Lean_Syntax_getArg(v_x_210_, v___x_217_);
        v___x_219_ = l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___closed__1;
        leanh::lean_inc(v___x_218_);
        v___x_220_ = l_Lean_Syntax_isOfKind(v___x_218_, v___x_219_);
        if v___x_220_ == 0 {
            let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_218_);
            leanh::lean_dec(v_x_210_);
            v___x_221_ = leanh::lean_box(0);
            v___x_222_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_222_, 0, v___x_221_);
            leanh::lean_ctor_set(v___x_222_, 1, v_a_212_);
            return v___x_222_;
        } else {
            let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_226_: u8 = 0;
            v___x_223_ = leanh::lean_unsigned_to_nat(1);
            v___x_224_ = l_Lean_Syntax_getArg(v_x_210_, v___x_223_);
            leanh::lean_dec(v_x_210_);
            v___x_225_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_224_);
            v___x_226_ = l_Lean_Syntax_matchesNull(v___x_224_, v___x_225_);
            if v___x_226_ == 0 {
                let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_224_);
                leanh::lean_dec(v___x_218_);
                v___x_227_ = leanh::lean_box(0);
                v___x_228_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_228_, 0, v___x_227_);
                leanh::lean_ctor_set(v___x_228_, 1, v_a_212_);
                return v___x_228_;
            } else {
                let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_231_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_232_: u8 = 0;
                let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_229_ = l_Lean_Syntax_getArg(v___x_224_, v___x_217_);
                v___x_230_ = l_Lean_Syntax_getArg(v___x_224_, v___x_223_);
                leanh::lean_dec(v___x_224_);
                v_ref_231_ = l_Lean_replaceRef(v___x_218_, v_a_211_);
                leanh::lean_dec(v___x_218_);
                v___x_232_ = 0;
                v___x_233_ = l_Lean_SourceInfo_fromRef(v_ref_231_, v___x_232_);
                leanh::lean_dec(v_ref_231_);
                v___x_234_ = l_Lean_Order_term___u21e8___00__closed__3;
                v___x_235_ = l_Lean_Order_term___u21e8___00__closed__6;
                leanh::lean_inc(v___x_233_);
                v___x_236_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_236_, 0, v___x_233_);
                leanh::lean_ctor_set(v___x_236_, 1, v___x_235_);
                v___x_237_ =
                    l_Lean_Syntax_node3(v___x_233_, v___x_234_, v___x_229_, v___x_236_, v___x_230_);
                v___x_238_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_238_, 0, v___x_237_);
                leanh::lean_ctor_set(v___x_238_, 1, v_a_212_);
                return v___x_238_;
            }
        }
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1___boxed(
    mut v_x_239_: *mut leanh::LeanObject,
    mut v_a_240_: *mut leanh::LeanObject,
    mut v_a_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Order___aux__Std__Internal__Do__Frame______unexpand__Lean__Order__himp__1(
        v_x_239_, v_a_240_, v_a_241_,
    );
    leanh::lean_dec(v_a_240_);
    return v_res_242_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_Frame(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_Assertion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_Frame(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_Do_Frame(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_Assertion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_Frame(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_Frame(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_Frame(builtin);
}