// Lean compiler output
// Module: Std.Internal.Do.Assertion
// Imports: Init.Internal.Order
use crate::r#gen::Init::Internal::Order::{
    initialize_Init_Internal_Order, runtime_initialize_Init_Internal_Order,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Name_mkStr5, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_unsigned_to_nat,
};
pub static l_Lean_Order_term_u22a4___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Order_term_u22a4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut LeanObject;
pub static l_Lean_Order_term_u22a4___closed__1_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Order_term_u22a4___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut LeanObject;
pub static l_Lean_Order_term_u22a4___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Order_term_u22a4___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__2_value) as *mut LeanObject;
static l_Lean_Order_term_u22a4___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Order_term_u22a4___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
pub static l_Lean_Order_term_u22a4___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__2_value) as *mut LeanObject,
        4896420126473035401 as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term_u22a4___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__3_value) as *mut LeanObject;
pub static l_Lean_Order_term_u22a4___closed__4_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Order_term_u22a4___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__4_value) as *mut LeanObject;
pub static l_Lean_Order_term_u22a4___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__4_value) as *mut LeanObject],
};
static mut l_Lean_Order_term_u22a4___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__5_value) as *mut LeanObject;
pub static l_Lean_Order_term_u22a4___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__3_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term_u22a4___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Order_term_u22a4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__6_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 111, 112, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0_value) as *mut LeanObject,4928918494582576983 as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__2_value) as *mut LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0_value) as *mut LeanObject,12247640180585144795 as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Order_term___u2293___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__0_value) as *mut LeanObject;
static l_Lean_Order_term___u2293___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Order_term___u2293___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
pub static l_Lean_Order_term___u2293___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__0_value) as *mut LeanObject,
        16606014227161981285 as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2293___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__1_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Order_term___u2293___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__2_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2293___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__4_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Order_term___u2293___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__4_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2293___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__5_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__6_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Order_term___u2293___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__6_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__6_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2293___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__7_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__7_value) as *mut LeanObject,
        (((71 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2293___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__8_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2293___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__9_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2293___00__closed__10_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__1_value) as *mut LeanObject,
        (((70 as usize) << 1) | 1) as *mut LeanObject,
        (((70 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2293___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__10_value) as *mut LeanObject;
pub static mut l_Lean_Order_term___u2293__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__10_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__2_value) as *mut LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__2_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 101, 116, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4_value) as *mut LeanObject;
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4_value) as *mut LeanObject,2741269361911581766 as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__6_value) as *mut LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4_value) as *mut LeanObject,12738217368988139970 as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__7_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__10_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__10_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Order_term___u2294___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__0_value) as *mut LeanObject;
static l_Lean_Order_term___u2294___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Order_term___u2294___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
pub static l_Lean_Order_term___u2294___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__0_value) as *mut LeanObject,
        15187416356175134241 as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2294___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__1_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Order_term___u2294___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__2_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2294___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__3_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__7_value) as *mut LeanObject,
        (((66 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2294___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__4_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2294___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__5_value) as *mut LeanObject;
pub static l_Lean_Order_term___u2294___00__closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__1_value) as *mut LeanObject,
        (((65 as usize) << 1) | 1) as *mut LeanObject,
        (((65 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Order_term___u2294___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Order_term___u2294__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Order_term___u2294___00__closed__6_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [106, 111, 105, 110, 0]};
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0_value) as *mut LeanObject,5607412979871164673 as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__2_value) as *mut LeanObject;
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order_term_u22a4___closed__1_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0_value) as *mut LeanObject,8142298027396223453 as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Order_instPartialOrderProp__std: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Order_instCompleteLatticeProp__std: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do_term_u231c___u231d___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Internal_Do_term_u231c___u231d___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__0_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__1_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Internal_Do_term_u231c___u231d___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__1_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__2_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Internal_Do_term_u231c___u231d___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__2_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__3_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Internal_Do_term_u231c___u231d___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__3_value) as *mut LeanObject;
static l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__1_value)
                as *mut LeanObject,
            1742885236933170401 as *mut LeanObject,
        ],
    };
static l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__2_value)
                as *mut LeanObject,
            1237304041707523237 as *mut LeanObject,
        ],
    };
pub static l_Std_Internal_Do_term_u231c___u231d___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__3_value)
                as *mut LeanObject,
            10911529642982843935 as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__5_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Internal_Do_term_u231c___u231d___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__5_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__6_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__7_value) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__7_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__8_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__9_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Internal_Do_term_u231c___u231d___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__9_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__10_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Order_term___u2293___00__closed__3_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__11_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u231c___u231d___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Do_term_u231c___u231d___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__12_value) as *mut LeanObject;
pub static mut l_Std_Internal_Do_term_u231c___u231d: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__12_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [65, 115, 115, 101, 114, 116, 105, 111, 110, 46, 111, 102, 80, 114, 111, 112, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__0_value) as *mut LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [65, 115, 115, 101, 114, 116, 105, 111, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 102, 80, 114, 111, 112, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2_value) as *mut LeanObject,12974967848607075472 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3_value) as *mut LeanObject,1342330347679651256 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__1_value) as *mut LeanObject,1742885236933170401 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u231c___u231d___closed__2_value) as *mut LeanObject,1237304041707523237 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__2_value) as *mut LeanObject,7306860446385387366 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__3_value) as *mut LeanObject,15310354355589681094 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__6_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__7_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1()
-> *mut LeanObject {
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_421_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__0;
    v___x_422_ = l_String_toRawSubstring_x27(v___x_421_);
    return v___x_422_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1(
    mut v_x_435_: *mut LeanObject,
    mut v_a_436_: *mut LeanObject,
    mut v_a_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: u8 = 0;
    v___x_438_ = l_Lean_Order_term_u22a4___closed__3;
    v___x_439_ = l_Lean_Syntax_isOfKind(v_x_435_, v___x_438_);
    if v___x_439_ == 0 {
        let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
        v___x_440_ = lean_box(1);
        v___x_441_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_441_, 0, v___x_440_);
        lean_ctor_set(v___x_441_, 1, v_a_437_);
        return v___x_441_;
    } else {
        let mut v_quotContext_442_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_443_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_445_: u8 = 0;
        let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_442_ = lean_ctor_get(v_a_436_, 1);
        v_currMacroScope_443_ = lean_ctor_get(v_a_436_, 2);
        v_ref_444_ = lean_ctor_get(v_a_436_, 5);
        v___x_445_ = 0;
        v___x_446_ = l_Lean_SourceInfo_fromRef(v_ref_444_, v___x_445_);
        v___x_447_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1_once), _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__1);
        v___x_448_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__2;
        lean_inc(v_currMacroScope_443_);
        lean_inc(v_quotContext_442_);
        v___x_449_ = l_Lean_addMacroScope(v_quotContext_442_, v___x_448_, v_currMacroScope_443_);
        v___x_450_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___closed__5;
        v___x_451_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_451_, 0, v___x_446_);
        lean_ctor_set(v___x_451_, 1, v___x_447_);
        lean_ctor_set(v___x_451_, 2, v___x_449_);
        lean_ctor_set(v___x_451_, 3, v___x_450_);
        v___x_452_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_452_, 0, v___x_451_);
        lean_ctor_set(v___x_452_, 1, v_a_437_);
        return v___x_452_;
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1___boxed(
    mut v_x_453_: *mut LeanObject,
    mut v_a_454_: *mut LeanObject,
    mut v_a_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_456_: *mut LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term_u22a4__1(v_x_453_, v_a_454_, v_a_455_);
    lean_dec_ref(v_a_454_);
    return v_res_456_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1(
    mut v_x_460_: *mut LeanObject,
    mut v_a_461_: *mut LeanObject,
    mut v_a_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: u8 = 0;
    v___x_463_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1;
    lean_inc(v_x_460_);
    v___x_464_ = l_Lean_Syntax_isOfKind(v_x_460_, v___x_463_);
    if v___x_464_ == 0 {
        let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_460_);
        v___x_465_ = lean_box(0);
        v___x_466_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_466_, 0, v___x_465_);
        lean_ctor_set(v___x_466_, 1, v_a_462_);
        return v___x_466_;
    } else {
        let mut v_ref_467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_468_: u8 = 0;
        let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
        v_ref_467_ = l_Lean_replaceRef(v_x_460_, v_a_461_);
        lean_dec(v_x_460_);
        v___x_468_ = 0;
        v___x_469_ = l_Lean_SourceInfo_fromRef(v_ref_467_, v___x_468_);
        lean_dec(v_ref_467_);
        v___x_470_ = l_Lean_Order_term_u22a4___closed__3;
        v___x_471_ = l_Lean_Order_term_u22a4___closed__4;
        lean_inc(v___x_469_);
        v___x_472_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_472_, 0, v___x_469_);
        lean_ctor_set(v___x_472_, 1, v___x_471_);
        v___x_473_ = l_Lean_Syntax_node1(v___x_469_, v___x_470_, v___x_472_);
        v___x_474_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_474_, 0, v___x_473_);
        lean_ctor_set(v___x_474_, 1, v_a_462_);
        return v___x_474_;
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___boxed(
    mut v_x_475_: *mut LeanObject,
    mut v_a_476_: *mut LeanObject,
    mut v_a_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_478_: *mut LeanObject = core::ptr::null_mut();
    v_res_478_ =
        l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1(
            v_x_475_, v_a_476_, v_a_477_,
        );
    lean_dec(v_a_476_);
    return v_res_478_;
}
pub unsafe fn _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5()
-> *mut LeanObject {
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    v___x_514_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__4;
    v___x_515_ = l_String_toRawSubstring_x27(v___x_514_);
    return v___x_515_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1(
    mut v_x_531_: *mut LeanObject,
    mut v_a_532_: *mut LeanObject,
    mut v_a_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    v___x_534_ = l_Lean_Order_term___u2293___00__closed__1;
    lean_inc(v_x_531_);
    v___x_535_ = l_Lean_Syntax_isOfKind(v_x_531_, v___x_534_);
    if v___x_535_ == 0 {
        let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_531_);
        v___x_536_ = lean_box(1);
        v___x_537_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_537_, 0, v___x_536_);
        lean_ctor_set(v___x_537_, 1, v_a_533_);
        return v___x_537_;
    } else {
        let mut v_quotContext_538_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_539_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_545_: u8 = 0;
        let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_538_ = lean_ctor_get(v_a_532_, 1);
        v_currMacroScope_539_ = lean_ctor_get(v_a_532_, 2);
        v_ref_540_ = lean_ctor_get(v_a_532_, 5);
        v___x_541_ = lean_unsigned_to_nat(0);
        v___x_542_ = l_Lean_Syntax_getArg(v_x_531_, v___x_541_);
        v___x_543_ = lean_unsigned_to_nat(2);
        v___x_544_ = l_Lean_Syntax_getArg(v_x_531_, v___x_543_);
        lean_dec(v_x_531_);
        v___x_545_ = 0;
        v___x_546_ = l_Lean_SourceInfo_fromRef(v_ref_540_, v___x_545_);
        v___x_547_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
        v___x_548_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5), core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5_once), _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__5);
        v___x_549_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__6;
        lean_inc(v_currMacroScope_539_);
        lean_inc(v_quotContext_538_);
        v___x_550_ = l_Lean_addMacroScope(v_quotContext_538_, v___x_549_, v_currMacroScope_539_);
        v___x_551_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__9;
        lean_inc_n(v___x_546_, 2);
        v___x_552_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_552_, 0, v___x_546_);
        lean_ctor_set(v___x_552_, 1, v___x_548_);
        lean_ctor_set(v___x_552_, 2, v___x_550_);
        lean_ctor_set(v___x_552_, 3, v___x_551_);
        v___x_553_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11;
        v___x_554_ = l_Lean_Syntax_node2(v___x_546_, v___x_553_, v___x_542_, v___x_544_);
        v___x_555_ = l_Lean_Syntax_node2(v___x_546_, v___x_547_, v___x_552_, v___x_554_);
        v___x_556_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_556_, 0, v___x_555_);
        lean_ctor_set(v___x_556_, 1, v_a_533_);
        return v___x_556_;
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___boxed(
    mut v_x_557_: *mut LeanObject,
    mut v_a_558_: *mut LeanObject,
    mut v_a_559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_560_: *mut LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1(v_x_557_, v_a_558_, v_a_559_);
    lean_dec_ref(v_a_558_);
    return v_res_560_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__meet__1(
    mut v_x_561_: *mut LeanObject,
    mut v_a_562_: *mut LeanObject,
    mut v_a_563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u8 = 0;
    v___x_564_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
    lean_inc(v_x_561_);
    v___x_565_ = l_Lean_Syntax_isOfKind(v_x_561_, v___x_564_);
    if v___x_565_ == 0 {
        let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_561_);
        v___x_566_ = lean_box(0);
        v___x_567_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_567_, 0, v___x_566_);
        lean_ctor_set(v___x_567_, 1, v_a_563_);
        return v___x_567_;
    } else {
        let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_571_: u8 = 0;
        v___x_568_ = lean_unsigned_to_nat(0);
        v___x_569_ = l_Lean_Syntax_getArg(v_x_561_, v___x_568_);
        v___x_570_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1;
        lean_inc(v___x_569_);
        v___x_571_ = l_Lean_Syntax_isOfKind(v___x_569_, v___x_570_);
        if v___x_571_ == 0 {
            let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_569_);
            lean_dec(v_x_561_);
            v___x_572_ = lean_box(0);
            v___x_573_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_573_, 0, v___x_572_);
            lean_ctor_set(v___x_573_, 1, v_a_563_);
            return v___x_573_;
        } else {
            let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_577_: u8 = 0;
            v___x_574_ = lean_unsigned_to_nat(1);
            v___x_575_ = l_Lean_Syntax_getArg(v_x_561_, v___x_574_);
            lean_dec(v_x_561_);
            v___x_576_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_575_);
            v___x_577_ = l_Lean_Syntax_matchesNull(v___x_575_, v___x_576_);
            if v___x_577_ == 0 {
                let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_575_);
                lean_dec(v___x_569_);
                v___x_578_ = lean_box(0);
                v___x_579_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_579_, 0, v___x_578_);
                lean_ctor_set(v___x_579_, 1, v_a_563_);
                return v___x_579_;
            } else {
                let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_582_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_583_: u8 = 0;
                let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
                v___x_580_ = l_Lean_Syntax_getArg(v___x_575_, v___x_568_);
                v___x_581_ = l_Lean_Syntax_getArg(v___x_575_, v___x_574_);
                lean_dec(v___x_575_);
                v_ref_582_ = l_Lean_replaceRef(v___x_569_, v_a_562_);
                lean_dec(v___x_569_);
                v___x_583_ = 0;
                v___x_584_ = l_Lean_SourceInfo_fromRef(v_ref_582_, v___x_583_);
                lean_dec(v_ref_582_);
                v___x_585_ = l_Lean_Order_term___u2293___00__closed__1;
                v___x_586_ = l_Lean_Order_term___u2293___00__closed__4;
                lean_inc(v___x_584_);
                v___x_587_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_587_, 0, v___x_584_);
                lean_ctor_set(v___x_587_, 1, v___x_586_);
                v___x_588_ =
                    l_Lean_Syntax_node3(v___x_584_, v___x_585_, v___x_580_, v___x_587_, v___x_581_);
                v___x_589_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_589_, 0, v___x_588_);
                lean_ctor_set(v___x_589_, 1, v_a_563_);
                return v___x_589_;
            }
        }
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__meet__1___boxed(
    mut v_x_590_: *mut LeanObject,
    mut v_a_591_: *mut LeanObject,
    mut v_a_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_593_: *mut LeanObject = core::ptr::null_mut();
    v_res_593_ =
        l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__meet__1(
            v_x_590_, v_a_591_, v_a_592_,
        );
    lean_dec(v_a_591_);
    return v_res_593_;
}
pub unsafe fn _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1()
-> *mut LeanObject {
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    v___x_615_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__0;
    v___x_616_ = l_String_toRawSubstring_x27(v___x_615_);
    return v___x_616_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1(
    mut v_x_629_: *mut LeanObject,
    mut v_a_630_: *mut LeanObject,
    mut v_a_631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: u8 = 0;
    v___x_632_ = l_Lean_Order_term___u2294___00__closed__1;
    lean_inc(v_x_629_);
    v___x_633_ = l_Lean_Syntax_isOfKind(v_x_629_, v___x_632_);
    if v___x_633_ == 0 {
        let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_629_);
        v___x_634_ = lean_box(1);
        v___x_635_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_635_, 0, v___x_634_);
        lean_ctor_set(v___x_635_, 1, v_a_631_);
        return v___x_635_;
    } else {
        let mut v_quotContext_636_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_637_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_638_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_643_: u8 = 0;
        let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_636_ = lean_ctor_get(v_a_630_, 1);
        v_currMacroScope_637_ = lean_ctor_get(v_a_630_, 2);
        v_ref_638_ = lean_ctor_get(v_a_630_, 5);
        v___x_639_ = lean_unsigned_to_nat(0);
        v___x_640_ = l_Lean_Syntax_getArg(v_x_629_, v___x_639_);
        v___x_641_ = lean_unsigned_to_nat(2);
        v___x_642_ = l_Lean_Syntax_getArg(v_x_629_, v___x_641_);
        lean_dec(v_x_629_);
        v___x_643_ = 0;
        v___x_644_ = l_Lean_SourceInfo_fromRef(v_ref_638_, v___x_643_);
        v___x_645_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
        v___x_646_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1), core::ptr::addr_of_mut!(l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1_once), _init_l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__1);
        v___x_647_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__2;
        lean_inc(v_currMacroScope_637_);
        lean_inc(v_quotContext_636_);
        v___x_648_ = l_Lean_addMacroScope(v_quotContext_636_, v___x_647_, v_currMacroScope_637_);
        v___x_649_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___closed__5;
        lean_inc_n(v___x_644_, 2);
        v___x_650_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_650_, 0, v___x_644_);
        lean_ctor_set(v___x_650_, 1, v___x_646_);
        lean_ctor_set(v___x_650_, 2, v___x_648_);
        lean_ctor_set(v___x_650_, 3, v___x_649_);
        v___x_651_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11;
        v___x_652_ = l_Lean_Syntax_node2(v___x_644_, v___x_651_, v___x_640_, v___x_642_);
        v___x_653_ = l_Lean_Syntax_node2(v___x_644_, v___x_645_, v___x_650_, v___x_652_);
        v___x_654_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_654_, 0, v___x_653_);
        lean_ctor_set(v___x_654_, 1, v_a_631_);
        return v___x_654_;
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1___boxed(
    mut v_x_655_: *mut LeanObject,
    mut v_a_656_: *mut LeanObject,
    mut v_a_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_658_: *mut LeanObject = core::ptr::null_mut();
    v_res_658_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2294____1(v_x_655_, v_a_656_, v_a_657_);
    lean_dec_ref(v_a_656_);
    return v_res_658_;
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__join__1(
    mut v_x_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: u8 = 0;
    v___x_662_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
    lean_inc(v_x_659_);
    v___x_663_ = l_Lean_Syntax_isOfKind(v_x_659_, v___x_662_);
    if v___x_663_ == 0 {
        let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_659_);
        v___x_664_ = lean_box(0);
        v___x_665_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_665_, 0, v___x_664_);
        lean_ctor_set(v___x_665_, 1, v_a_661_);
        return v___x_665_;
    } else {
        let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_669_: u8 = 0;
        v___x_666_ = lean_unsigned_to_nat(0);
        v___x_667_ = l_Lean_Syntax_getArg(v_x_659_, v___x_666_);
        v___x_668_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1;
        lean_inc(v___x_667_);
        v___x_669_ = l_Lean_Syntax_isOfKind(v___x_667_, v___x_668_);
        if v___x_669_ == 0 {
            let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_667_);
            lean_dec(v_x_659_);
            v___x_670_ = lean_box(0);
            v___x_671_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_671_, 0, v___x_670_);
            lean_ctor_set(v___x_671_, 1, v_a_661_);
            return v___x_671_;
        } else {
            let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_675_: u8 = 0;
            v___x_672_ = lean_unsigned_to_nat(1);
            v___x_673_ = l_Lean_Syntax_getArg(v_x_659_, v___x_672_);
            lean_dec(v_x_659_);
            v___x_674_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_673_);
            v___x_675_ = l_Lean_Syntax_matchesNull(v___x_673_, v___x_674_);
            if v___x_675_ == 0 {
                let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_673_);
                lean_dec(v___x_667_);
                v___x_676_ = lean_box(0);
                v___x_677_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_677_, 0, v___x_676_);
                lean_ctor_set(v___x_677_, 1, v_a_661_);
                return v___x_677_;
            } else {
                let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_680_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_681_: u8 = 0;
                let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
                v___x_678_ = l_Lean_Syntax_getArg(v___x_673_, v___x_666_);
                v___x_679_ = l_Lean_Syntax_getArg(v___x_673_, v___x_672_);
                lean_dec(v___x_673_);
                v_ref_680_ = l_Lean_replaceRef(v___x_667_, v_a_660_);
                lean_dec(v___x_667_);
                v___x_681_ = 0;
                v___x_682_ = l_Lean_SourceInfo_fromRef(v_ref_680_, v___x_681_);
                lean_dec(v_ref_680_);
                v___x_683_ = l_Lean_Order_term___u2294___00__closed__1;
                v___x_684_ = l_Lean_Order_term___u2294___00__closed__2;
                lean_inc(v___x_682_);
                v___x_685_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_685_, 0, v___x_682_);
                lean_ctor_set(v___x_685_, 1, v___x_684_);
                v___x_686_ =
                    l_Lean_Syntax_node3(v___x_682_, v___x_683_, v___x_678_, v___x_685_, v___x_679_);
                v___x_687_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_687_, 0, v___x_686_);
                lean_ctor_set(v___x_687_, 1, v_a_661_);
                return v___x_687_;
            }
        }
    }
}
pub unsafe fn l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__join__1___boxed(
    mut v_x_688_: *mut LeanObject,
    mut v_a_689_: *mut LeanObject,
    mut v_a_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_691_: *mut LeanObject = core::ptr::null_mut();
    v_res_691_ =
        l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__join__1(
            v_x_688_, v_a_689_, v_a_690_,
        );
    lean_dec(v_a_689_);
    return v_res_691_;
}
pub unsafe fn _init_l_Lean_Order_instPartialOrderProp__std() -> *mut LeanObject {
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    v___x_692_ = lean_box(0);
    return v___x_692_;
}
pub unsafe fn _init_l_Lean_Order_instCompleteLatticeProp__std() -> *mut LeanObject {
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    v___x_693_ = lean_box(0);
    return v___x_693_;
}
pub unsafe fn l_Std_Internal_Do_instCCPOOfAssertion___redArg(
    mut v_inst_694_: *mut LeanObject,
) -> *mut LeanObject {
    return v_inst_694_;
}
pub unsafe fn l_Std_Internal_Do_instCCPOOfAssertion(
    mut v_EPred_695_: *mut LeanObject,
    mut v_inst_696_: *mut LeanObject,
) -> *mut LeanObject {
    return v_inst_696_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1()
-> *mut LeanObject {
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    v___x_729_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__0;
    v___x_730_ = l_String_toRawSubstring_x27(v___x_729_);
    return v___x_730_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1(
    mut v_x_748_: *mut LeanObject,
    mut v_a_749_: *mut LeanObject,
    mut v_a_750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: u8 = 0;
    v___x_751_ = l_Std_Internal_Do_term_u231c___u231d___closed__4;
    lean_inc(v_x_748_);
    v___x_752_ = l_Lean_Syntax_isOfKind(v_x_748_, v___x_751_);
    if v___x_752_ == 0 {
        let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_748_);
        v___x_753_ = lean_box(1);
        v___x_754_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_754_, 0, v___x_753_);
        lean_ctor_set(v___x_754_, 1, v_a_750_);
        return v___x_754_;
    } else {
        let mut v_quotContext_755_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_756_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_760_: u8 = 0;
        let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_755_ = lean_ctor_get(v_a_749_, 1);
        v_currMacroScope_756_ = lean_ctor_get(v_a_749_, 2);
        v_ref_757_ = lean_ctor_get(v_a_749_, 5);
        v___x_758_ = lean_unsigned_to_nat(1);
        v___x_759_ = l_Lean_Syntax_getArg(v_x_748_, v___x_758_);
        lean_dec(v_x_748_);
        v___x_760_ = 0;
        v___x_761_ = l_Lean_SourceInfo_fromRef(v_ref_757_, v___x_760_);
        v___x_762_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
        v___x_763_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__1);
        v___x_764_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__4;
        lean_inc(v_currMacroScope_756_);
        lean_inc(v_quotContext_755_);
        v___x_765_ = l_Lean_addMacroScope(v_quotContext_755_, v___x_764_, v_currMacroScope_756_);
        v___x_766_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___closed__7;
        lean_inc_n(v___x_761_, 2);
        v___x_767_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_767_, 0, v___x_761_);
        lean_ctor_set(v___x_767_, 1, v___x_763_);
        lean_ctor_set(v___x_767_, 2, v___x_765_);
        lean_ctor_set(v___x_767_, 3, v___x_766_);
        v___x_768_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__11;
        v___x_769_ = l_Lean_Syntax_node1(v___x_761_, v___x_768_, v___x_759_);
        v___x_770_ = l_Lean_Syntax_node2(v___x_761_, v___x_762_, v___x_767_, v___x_769_);
        v___x_771_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_771_, 0, v___x_770_);
        lean_ctor_set(v___x_771_, 1, v_a_750_);
        return v___x_771_;
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1___boxed(
    mut v_x_772_: *mut LeanObject,
    mut v_a_773_: *mut LeanObject,
    mut v_a_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_775_: *mut LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______macroRules__Std__Internal__Do__term_u231c___u231d__1(v_x_772_, v_a_773_, v_a_774_);
    lean_dec_ref(v_a_773_);
    return v_res_775_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______unexpand__Std__Internal__Do__Assertion__ofProp__1(
    mut v_x_776_: *mut LeanObject,
    mut v_a_777_: *mut LeanObject,
    mut v_a_778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: u8 = 0;
    v___x_779_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______macroRules__Lean__Order__term___u2293____1___closed__3;
    lean_inc(v_x_776_);
    v___x_780_ = l_Lean_Syntax_isOfKind(v_x_776_, v___x_779_);
    if v___x_780_ == 0 {
        let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_776_);
        v___x_781_ = lean_box(0);
        v___x_782_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_782_, 0, v___x_781_);
        lean_ctor_set(v___x_782_, 1, v_a_778_);
        return v___x_782_;
    } else {
        let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_786_: u8 = 0;
        v___x_783_ = lean_unsigned_to_nat(0);
        v___x_784_ = l_Lean_Syntax_getArg(v_x_776_, v___x_783_);
        v___x_785_ = l_Lean_Order___aux__Std__Internal__Do__Assertion______unexpand__Lean__Order__top__1___closed__1;
        lean_inc(v___x_784_);
        v___x_786_ = l_Lean_Syntax_isOfKind(v___x_784_, v___x_785_);
        if v___x_786_ == 0 {
            let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_784_);
            lean_dec(v_x_776_);
            v___x_787_ = lean_box(0);
            v___x_788_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_788_, 0, v___x_787_);
            lean_ctor_set(v___x_788_, 1, v_a_778_);
            return v___x_788_;
        } else {
            let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_791_: u8 = 0;
            v___x_789_ = lean_unsigned_to_nat(1);
            v___x_790_ = l_Lean_Syntax_getArg(v_x_776_, v___x_789_);
            lean_dec(v_x_776_);
            lean_inc(v___x_790_);
            v___x_791_ = l_Lean_Syntax_matchesNull(v___x_790_, v___x_789_);
            if v___x_791_ == 0 {
                let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_790_);
                lean_dec(v___x_784_);
                v___x_792_ = lean_box(0);
                v___x_793_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_793_, 0, v___x_792_);
                lean_ctor_set(v___x_793_, 1, v_a_778_);
                return v___x_793_;
            } else {
                let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_795_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_796_: u8 = 0;
                let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
                v___x_794_ = l_Lean_Syntax_getArg(v___x_790_, v___x_783_);
                lean_dec(v___x_790_);
                v_ref_795_ = l_Lean_replaceRef(v___x_784_, v_a_777_);
                lean_dec(v___x_784_);
                v___x_796_ = 0;
                v___x_797_ = l_Lean_SourceInfo_fromRef(v_ref_795_, v___x_796_);
                lean_dec(v_ref_795_);
                v___x_798_ = l_Std_Internal_Do_term_u231c___u231d___closed__4;
                v___x_799_ = l_Std_Internal_Do_term_u231c___u231d___closed__5;
                lean_inc_n(v___x_797_, 2);
                v___x_800_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_800_, 0, v___x_797_);
                lean_ctor_set(v___x_800_, 1, v___x_799_);
                v___x_801_ = l_Std_Internal_Do_term_u231c___u231d___closed__9;
                v___x_802_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_802_, 0, v___x_797_);
                lean_ctor_set(v___x_802_, 1, v___x_801_);
                v___x_803_ =
                    l_Lean_Syntax_node3(v___x_797_, v___x_798_, v___x_800_, v___x_794_, v___x_802_);
                v___x_804_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_804_, 0, v___x_803_);
                lean_ctor_set(v___x_804_, 1, v_a_778_);
                return v___x_804_;
            }
        }
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______unexpand__Std__Internal__Do__Assertion__ofProp__1___boxed(
    mut v_x_805_: *mut LeanObject,
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_808_: *mut LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Std_Internal_Do___aux__Std__Internal__Do__Assertion______unexpand__Std__Internal__Do__Assertion__ofProp__1(v_x_805_, v_a_806_, v_a_807_);
    lean_dec(v_a_806_);
    return v_res_808_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_Assertion(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Internal_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Order_instPartialOrderProp__std = _init_l_Lean_Order_instPartialOrderProp__std();
    lean_mark_persistent(l_Lean_Order_instPartialOrderProp__std);
    l_Lean_Order_instCompleteLatticeProp__std = _init_l_Lean_Order_instCompleteLatticeProp__std();
    lean_mark_persistent(l_Lean_Order_instCompleteLatticeProp__std);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_Assertion(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_Do_Assertion(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Internal_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_Assertion(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_Assertion(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Internal_Do_Assertion(builtin);
}
