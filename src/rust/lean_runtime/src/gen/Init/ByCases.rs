// Lean compiler output
// Module: Init.ByCases
// Imports: Init.Grind.Tactics Init.Grind.Tactics Init.SimpLemmas
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, meta_initialize_Init_Grind_Tactics,
    runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node8,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::SimpLemmas::{
    initialize_Init_SimpLemmas, runtime_initialize_Init_SimpLemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
pub static l_tacticBy__cases___x3a___00__closed__0_value: LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        116, 97, 99, 116, 105, 99, 66, 121, 95, 99, 97, 115, 101, 115, 95, 58, 95, 0,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__0_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__0_value) as *mut LeanObject,
        10022184304783606268 as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__1_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__2_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_tacticBy__cases___x3a___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__2_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__3_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__4_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [98, 121, 95, 99, 97, 115, 101, 115, 32, 0],
};
static mut l_tacticBy__cases___x3a___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__4_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__4_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__5_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__6_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_tacticBy__cases___x3a___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__6_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__6_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__7_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__8_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [97, 116, 111, 109, 105, 99, 0],
};
static mut l_tacticBy__cases___x3a___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__8_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__8_value) as *mut LeanObject,
        4024150434455327032 as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__9_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__10_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_tacticBy__cases___x3a___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__10_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__11_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__10_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__11_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__12_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__11_value) as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__12_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__13_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 32, 0],
};
static mut l_tacticBy__cases___x3a___00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__13_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__14_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__13_value) as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__14_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__14_value) as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__15_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__16_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__15_value) as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__16_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__17_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__16_value) as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__17_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__18_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__17_value) as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__18_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__19_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_tacticBy__cases___x3a___00__closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__19_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__20_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__19_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__20_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__21_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__20_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__21_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__22_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__18_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__21_value) as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__22_value) as *mut LeanObject;
pub static l_tacticBy__cases___x3a___00__closed__23_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__22_value) as *mut LeanObject,
    ],
};
static mut l_tacticBy__cases___x3a___00__closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__23_value) as *mut LeanObject;
pub static mut l_tacticBy__cases___x3a__: *mut LeanObject =
    core::ptr::addr_of!(l_tacticBy__cases___x3a___00__closed__23_value) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 121, 95, 99, 97, 115, 101, 115, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__0_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__1_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__1_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [104, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3_value
) as *mut LeanObject;
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3_value
        ) as *mut LeanObject,
        8738205681931236784 as *mut LeanObject,
    ],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
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
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [111, 112, 101, 110, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3_value
) as *mut LeanObject;
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3_value) as *mut LeanObject,1617625281282625860 as *mut LeanObject] };
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__5_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__5_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__6_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [111, 112, 101, 110, 83, 105, 109, 112, 108, 101, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__6_value
) as *mut LeanObject;
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__6_value) as *mut LeanObject,4840083868155834027 as *mut LeanObject] };
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8_value
) as *mut LeanObject;
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8_value
        ) as *mut LeanObject,
        10854111772627758120 as *mut LeanObject,
    ],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10_value
    ) as *mut LeanObject],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__11_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__12_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__11_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__12_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__13_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [105, 110, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__13_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__14_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__14_value
) as *mut LeanObject;
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__14_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__16_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__16_value
) as *mut LeanObject;
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__16_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [114, 101, 102, 105, 110, 101, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18_value
) as *mut LeanObject;
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18_value) as *mut LeanObject,17704266427038597681 as *mut LeanObject] };
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__20_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        116, 101, 114, 109, 68, 101, 112, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0,
    ],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__20_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__21_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__20_value
        ) as *mut LeanObject,
        12532511233276993215 as *mut LeanObject,
    ],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__21_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__22_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [105, 102, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__22_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__23_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__23_value
) as *mut LeanObject;
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__23_value) as *mut LeanObject,13771926289831477797 as *mut LeanObject] };
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__25_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 104, 101, 110, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__25_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__26_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__26_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__27_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0,
    ],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__27_value
) as *mut LeanObject;
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__26_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__27_value) as *mut LeanObject,11921244625177918938 as *mut LeanObject] };
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__29_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [63, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__29_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [112, 111, 115, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30_value
) as *mut LeanObject;
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30_value
        ) as *mut LeanObject,
        6391873163851744175 as *mut LeanObject,
    ],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [101, 108, 115, 101, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33_value
) as *mut LeanObject;
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 101, 103, 0],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34_value
) as *mut LeanObject;
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34_value
        ) as *mut LeanObject,
        7212229036697944544 as *mut LeanObject,
    ],
};
static mut l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36_value
) as *mut LeanObject;
pub unsafe fn _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4()
-> *mut LeanObject {
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    v___x_308_ = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__3;
    v___x_309_ = l_String_toRawSubstring_x27(v___x_308_);
    return v___x_309_;
}
pub unsafe fn l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1(
    mut v_x_313_: *mut LeanObject,
    mut v_a_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: u8 = 0;
    v___x_316_ = l_tacticBy__cases___x3a___00__closed__1;
    lean_inc(v_x_313_);
    v___x_317_ = l_Lean_Syntax_isOfKind(v_x_313_, v___x_316_);
    if v___x_317_ == 0 {
        let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_313_);
        v___x_318_ = lean_box(1);
        v___x_319_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_319_, 0, v___x_318_);
        lean_ctor_set(v___x_319_, 1, v_a_315_);
        return v___x_319_;
    } else {
        let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_323_: u8 = 0;
        v___x_320_ = lean_unsigned_to_nat(0);
        v___x_321_ = lean_unsigned_to_nat(1);
        v___x_322_ = l_Lean_Syntax_getArg(v_x_313_, v___x_321_);
        v___x_323_ = l_Lean_Syntax_matchesNull(v___x_322_, v___x_320_);
        if v___x_323_ == 0 {
            let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_313_);
            v___x_324_ = lean_box(1);
            v___x_325_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_325_, 0, v___x_324_);
            lean_ctor_set(v___x_325_, 1, v_a_315_);
            return v___x_325_;
        } else {
            let mut v_quotContext_326_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_327_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_328_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_331_: u8 = 0;
            let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_326_ = lean_ctor_get(v_a_314_, 1);
            v_currMacroScope_327_ = lean_ctor_get(v_a_314_, 2);
            v_ref_328_ = lean_ctor_get(v_a_314_, 5);
            v___x_329_ = lean_unsigned_to_nat(2);
            v___x_330_ = l_Lean_Syntax_getArg(v_x_313_, v___x_329_);
            lean_dec(v_x_313_);
            v___x_331_ = 0;
            v___x_332_ = l_Lean_SourceInfo_fromRef(v_ref_328_, v___x_331_);
            v___x_333_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__0;
            lean_inc_n(v___x_332_, 4);
            v___x_334_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_334_, 0, v___x_332_);
            lean_ctor_set(v___x_334_, 1, v___x_333_);
            v___x_335_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2;
            v___x_336_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4), core::ptr::addr_of_mut!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4_once), _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__4);
            v___x_337_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__5;
            lean_inc(v_currMacroScope_327_);
            lean_inc(v_quotContext_326_);
            v___x_338_ =
                l_Lean_addMacroScope(v_quotContext_326_, v___x_337_, v_currMacroScope_327_);
            v___x_339_ = lean_box(0);
            v___x_340_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_340_, 0, v___x_332_);
            lean_ctor_set(v___x_340_, 1, v___x_336_);
            lean_ctor_set(v___x_340_, 2, v___x_338_);
            lean_ctor_set(v___x_340_, 3, v___x_339_);
            v___x_341_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6;
            v___x_342_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_342_, 0, v___x_332_);
            lean_ctor_set(v___x_342_, 1, v___x_341_);
            v___x_343_ = l_Lean_Syntax_node2(v___x_332_, v___x_335_, v___x_340_, v___x_342_);
            v___x_344_ =
                l_Lean_Syntax_node3(v___x_332_, v___x_316_, v___x_334_, v___x_343_, v___x_330_);
            v___x_345_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_345_, 0, v___x_344_);
            lean_ctor_set(v___x_345_, 1, v_a_315_);
            return v___x_345_;
        }
    }
}
pub unsafe fn l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___boxed(
    mut v_x_346_: *mut LeanObject,
    mut v_a_347_: *mut LeanObject,
    mut v_a_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_349_: *mut LeanObject = core::ptr::null_mut();
    v_res_349_ = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1(
        v_x_346_, v_a_347_, v_a_348_,
    );
    lean_dec_ref(v_a_347_);
    return v_res_349_;
}
pub unsafe fn _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9()
-> *mut LeanObject {
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    v___x_367_ = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__8;
    v___x_368_ = l_String_toRawSubstring_x27(v___x_367_);
    return v___x_368_;
}
pub unsafe fn _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31()
-> *mut LeanObject {
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    v___x_413_ = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__30;
    v___x_414_ = l_String_toRawSubstring_x27(v___x_413_);
    return v___x_414_;
}
pub unsafe fn _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35()
-> *mut LeanObject {
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    v___x_419_ = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__34;
    v___x_420_ = l_String_toRawSubstring_x27(v___x_419_);
    return v___x_420_;
}
pub unsafe fn l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2(
    mut v_x_423_: *mut LeanObject,
    mut v_a_424_: *mut LeanObject,
    mut v_a_425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: u8 = 0;
    v___x_426_ = l_tacticBy__cases___x3a___00__closed__1;
    lean_inc(v_x_423_);
    v___x_427_ = l_Lean_Syntax_isOfKind(v_x_423_, v___x_426_);
    if v___x_427_ == 0 {
        let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_423_);
        v___x_428_ = lean_box(1);
        v___x_429_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_429_, 0, v___x_428_);
        lean_ctor_set(v___x_429_, 1, v_a_425_);
        return v___x_429_;
    } else {
        let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_433_: u8 = 0;
        v___x_430_ = lean_unsigned_to_nat(1);
        v___x_431_ = l_Lean_Syntax_getArg(v_x_423_, v___x_430_);
        v___x_432_ = lean_unsigned_to_nat(2);
        lean_inc(v___x_431_);
        v___x_433_ = l_Lean_Syntax_matchesNull(v___x_431_, v___x_432_);
        if v___x_433_ == 0 {
            let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_431_);
            lean_dec(v_x_423_);
            v___x_434_ = lean_box(1);
            v___x_435_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_435_, 0, v___x_434_);
            lean_ctor_set(v___x_435_, 1, v_a_425_);
            return v___x_435_;
        } else {
            let mut v_quotContext_436_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_437_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_438_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_442_: u8 = 0;
            let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
            v_quotContext_436_ = lean_ctor_get(v_a_424_, 1);
            v_currMacroScope_437_ = lean_ctor_get(v_a_424_, 2);
            v_ref_438_ = lean_ctor_get(v_a_424_, 5);
            v___x_439_ = lean_unsigned_to_nat(0);
            v___x_440_ = l_Lean_Syntax_getArg(v___x_431_, v___x_439_);
            lean_dec(v___x_431_);
            v___x_441_ = l_Lean_Syntax_getArg(v_x_423_, v___x_432_);
            lean_dec(v_x_423_);
            v___x_442_ = 0;
            v___x_443_ = l_Lean_SourceInfo_fromRef(v_ref_438_, v___x_442_);
            v___x_444_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__3;
            v___x_445_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__4;
            lean_inc_n(v___x_443_, 21);
            v___x_446_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_446_, 0, v___x_443_);
            lean_ctor_set(v___x_446_, 1, v___x_444_);
            v___x_447_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__7;
            v___x_448_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__2;
            v___x_449_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9), core::ptr::addr_of_mut!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9_once), _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__9);
            v___x_450_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__10;
            lean_inc_n(v_currMacroScope_437_, 3);
            lean_inc_n(v_quotContext_436_, 3);
            v___x_451_ =
                l_Lean_addMacroScope(v_quotContext_436_, v___x_450_, v_currMacroScope_437_);
            v___x_452_ = lean_box(0);
            v___x_453_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__12;
            v___x_454_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_454_, 0, v___x_443_);
            lean_ctor_set(v___x_454_, 1, v___x_449_);
            lean_ctor_set(v___x_454_, 2, v___x_451_);
            lean_ctor_set(v___x_454_, 3, v___x_453_);
            v___x_455_ = l_Lean_Syntax_node1(v___x_443_, v___x_448_, v___x_454_);
            v___x_456_ = l_Lean_Syntax_node1(v___x_443_, v___x_447_, v___x_455_);
            v___x_457_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__13;
            v___x_458_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_458_, 0, v___x_443_);
            lean_ctor_set(v___x_458_, 1, v___x_457_);
            v___x_459_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__15;
            v___x_460_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__17;
            v___x_461_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__18;
            v___x_462_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__19;
            v___x_463_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_463_, 0, v___x_443_);
            lean_ctor_set(v___x_463_, 1, v___x_461_);
            v___x_464_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__21;
            v___x_465_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__22;
            v___x_466_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_466_, 0, v___x_443_);
            lean_ctor_set(v___x_466_, 1, v___x_465_);
            v___x_467_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__24;
            v___x_468_ = l_Lean_Syntax_node1(v___x_443_, v___x_467_, v___x_440_);
            v___x_469_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1___closed__6;
            v___x_470_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_470_, 0, v___x_443_);
            lean_ctor_set(v___x_470_, 1, v___x_469_);
            v___x_471_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__25;
            v___x_472_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_472_, 0, v___x_443_);
            lean_ctor_set(v___x_472_, 1, v___x_471_);
            v___x_473_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__28;
            v___x_474_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__29;
            v___x_475_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_475_, 0, v___x_443_);
            lean_ctor_set(v___x_475_, 1, v___x_474_);
            v___x_476_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31), core::ptr::addr_of_mut!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31_once), _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__31);
            v___x_477_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__32;
            v___x_478_ =
                l_Lean_addMacroScope(v_quotContext_436_, v___x_477_, v_currMacroScope_437_);
            v___x_479_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_479_, 0, v___x_443_);
            lean_ctor_set(v___x_479_, 1, v___x_476_);
            lean_ctor_set(v___x_479_, 2, v___x_478_);
            lean_ctor_set(v___x_479_, 3, v___x_452_);
            lean_inc_ref(v___x_475_);
            v___x_480_ = l_Lean_Syntax_node2(v___x_443_, v___x_473_, v___x_475_, v___x_479_);
            v___x_481_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__33;
            v___x_482_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_482_, 0, v___x_443_);
            lean_ctor_set(v___x_482_, 1, v___x_481_);
            v___x_483_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35), core::ptr::addr_of_mut!(l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35_once), _init_l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__35);
            v___x_484_ =
                l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___closed__36;
            v___x_485_ =
                l_Lean_addMacroScope(v_quotContext_436_, v___x_484_, v_currMacroScope_437_);
            v___x_486_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_486_, 0, v___x_443_);
            lean_ctor_set(v___x_486_, 1, v___x_483_);
            lean_ctor_set(v___x_486_, 2, v___x_485_);
            lean_ctor_set(v___x_486_, 3, v___x_452_);
            v___x_487_ = l_Lean_Syntax_node2(v___x_443_, v___x_473_, v___x_475_, v___x_486_);
            v___x_488_ = l_Lean_Syntax_node8(
                v___x_443_, v___x_464_, v___x_466_, v___x_468_, v___x_470_, v___x_441_, v___x_472_,
                v___x_480_, v___x_482_, v___x_487_,
            );
            v___x_489_ = l_Lean_Syntax_node2(v___x_443_, v___x_462_, v___x_463_, v___x_488_);
            v___x_490_ = l_Lean_Syntax_node1(v___x_443_, v___x_448_, v___x_489_);
            v___x_491_ = l_Lean_Syntax_node1(v___x_443_, v___x_460_, v___x_490_);
            v___x_492_ = l_Lean_Syntax_node1(v___x_443_, v___x_459_, v___x_491_);
            v___x_493_ = l_Lean_Syntax_node4(
                v___x_443_, v___x_445_, v___x_446_, v___x_456_, v___x_458_, v___x_492_,
            );
            v___x_494_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_494_, 0, v___x_493_);
            lean_ctor_set(v___x_494_, 1, v_a_425_);
            return v___x_494_;
        }
    }
}
pub unsafe fn l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2___boxed(
    mut v_x_495_: *mut LeanObject,
    mut v_a_496_: *mut LeanObject,
    mut v_a_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_498_: *mut LeanObject = core::ptr::null_mut();
    v_res_498_ = l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2(
        v_x_495_, v_a_496_, v_a_497_,
    );
    lean_dec_ref(v_a_496_);
    return v_res_498_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_ByCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_ByCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_ByCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_ByCases(builtin);
}
