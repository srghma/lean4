// Lean compiler output
// Module: Init.WFTactics
// Imports: Init.WF Init.Data.Nat.Basic
use crate::r#gen::Init::Data::Nat::Basic::{
    initialize_Init_Data_Nat_Basic, runtime_initialize_Init_Data_Nat_Basic,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node6,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::WF::{initialize_Init_WF, runtime_initialize_Init_WF};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
pub static l_tacticSimp__wf___closed__0_value: LeanStringObject<14> = LeanStringObject {
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
        116, 97, 99, 116, 105, 99, 83, 105, 109, 112, 95, 119, 102, 0,
    ],
};
static mut l_tacticSimp__wf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tacticSimp__wf___closed__0_value) as *mut LeanObject;
pub static l_tacticSimp__wf___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticSimp__wf___closed__0_value) as *mut LeanObject,
        17997176516580445922 as *mut LeanObject,
    ],
};
static mut l_tacticSimp__wf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_tacticSimp__wf___closed__1_value) as *mut LeanObject;
pub static l_tacticSimp__wf___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 105, 109, 112, 95, 119, 102, 0],
};
static mut l_tacticSimp__wf___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_tacticSimp__wf___closed__2_value) as *mut LeanObject;
pub static l_tacticSimp__wf___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticSimp__wf___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_tacticSimp__wf___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_tacticSimp__wf___closed__3_value) as *mut LeanObject;
pub static l_tacticSimp__wf___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticSimp__wf___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticSimp__wf___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_tacticSimp__wf___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_tacticSimp__wf___closed__4_value) as *mut LeanObject;
pub static mut l_tacticSimp__wf: *mut LeanObject =
    core::ptr::addr_of!(l_tacticSimp__wf___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value:
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
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value:
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
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value:
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
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 84, 114, 121, 95, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__3_value
        ) as *mut LeanObject,
        10962186005905108258 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5_value:
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
    m_data: [116, 114, 121, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6_value:
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
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6_value
        ) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8_value:
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
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__8_value
        ) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10_value:
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
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__10_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12_value:
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
    m_data: [115, 105, 109, 112, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12_value
        ) as *mut LeanObject,
        12783917532758215986 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__14_value
        ) as *mut LeanObject,
        3488656302031949961 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16_value:
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
    m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__16_value
        ) as *mut LeanObject,
        10138443044734372301 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18_value:
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
        112, 111, 115, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__18_value
        ) as *mut LeanObject,
        9555431800314169832 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20_value:
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
    m_data: [43, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21_value:
    LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        117, 110, 102, 111, 108, 100, 80, 97, 114, 116, 105, 97, 108, 65, 112, 112, 0,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21_value
        ) as *mut LeanObject,
        15549944650758933297 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24_value:
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
    m_data: [122, 101, 116, 97, 68, 101, 108, 116, 97, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24_value
        ) as *mut LeanObject,
        1066184292711288961 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28_value:
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
    m_data: [91, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29_value:
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
    m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__29_value
        ) as *mut LeanObject,
        7383208167966365478 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31_value:
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
    m_data: [105, 110, 118, 73, 109, 97, 103, 101, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31_value
        ) as *mut LeanObject,
        3221764316860498547 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__34_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36_value:
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
    m_data: [44, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37_value:
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
    m_data: [73, 110, 118, 73, 109, 97, 103, 101, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37_value
        ) as *mut LeanObject,
        3591533214446369163 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41_value:
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
        l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39_value
    ) as *mut LeanObject],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__41_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__40_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__42_value
        ) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44_value:
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
    m_data: [80, 114, 111, 100, 46, 108, 101, 120, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value:
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
    m_data: [80, 114, 111, 100, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47_value:
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
    m_data: [108, 101, 120, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value
        ) as *mut LeanObject,
        15289851429949568889 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__47_value
        ) as *mut LeanObject,
        17253982048723950278 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50_value:
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
        l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48_value
    ) as *mut LeanObject],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__50_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__49_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__51_value
        ) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53_value:
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
    m_data: [115, 105, 122, 101, 79, 102, 87, 70, 82, 101, 108, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53_value
        ) as *mut LeanObject,
        7548106692965060290 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__56_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58_value:
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
    m_data: [109, 101, 97, 115, 117, 114, 101, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58_value
        ) as *mut LeanObject,
        5951634441853730580 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__61_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [78, 97, 116, 46, 108, 116, 95, 119, 102, 82, 101, 108, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value:
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
    m_data: [78, 97, 116, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66_value:
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
    m_data: [108, 116, 95, 119, 102, 82, 101, 108, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value
        ) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__66_value
        ) as *mut LeanObject,
        5776423399683745690 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__68_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70_value:
    LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        87, 101, 108, 108, 70, 111, 117, 110, 100, 101, 100, 82, 101, 108, 97, 116, 105, 111, 110,
        46, 114, 101, 108, 0,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        87, 101, 108, 108, 70, 111, 117, 110, 100, 101, 100, 82, 101, 108, 97, 116, 105, 111, 110,
        0,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73_value:
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
    m_data: [114, 101, 108, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__72_value
        ) as *mut LeanObject,
        3429923986742416119 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__73_value
        ) as *mut LeanObject,
        5903757612723289493 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76_value:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__75_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77_value:
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
    m_data: [93, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77_value
) as *mut LeanObject;
pub static l_tacticClean__wf___closed__0_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        116, 97, 99, 116, 105, 99, 67, 108, 101, 97, 110, 95, 119, 102, 0,
    ],
};
static mut l_tacticClean__wf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tacticClean__wf___closed__0_value) as *mut LeanObject;
pub static l_tacticClean__wf___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticClean__wf___closed__0_value) as *mut LeanObject,
        11462525315186813201 as *mut LeanObject,
    ],
};
static mut l_tacticClean__wf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_tacticClean__wf___closed__1_value) as *mut LeanObject;
pub static l_tacticClean__wf___closed__2_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 108, 101, 97, 110, 95, 119, 102, 0],
};
static mut l_tacticClean__wf___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_tacticClean__wf___closed__2_value) as *mut LeanObject;
pub static l_tacticClean__wf___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticClean__wf___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_tacticClean__wf___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_tacticClean__wf___closed__3_value) as *mut LeanObject;
pub static l_tacticClean__wf___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticClean__wf___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticClean__wf___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_tacticClean__wf___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_tacticClean__wf___closed__4_value) as *mut LeanObject;
pub static mut l_tacticClean__wf: *mut LeanObject =
    core::ptr::addr_of!(l_tacticClean__wf___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__0_value:
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
        110, 101, 103, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__0_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_0:
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value:
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
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__0_value
        ) as *mut LeanObject,
        15975902816121986500 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2_value:
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
    m_data: [45, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        102, 97, 105, 108, 73, 102, 85, 110, 99, 104, 97, 110, 103, 101, 100, 0,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5_value:
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
            l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3_value
        ) as *mut LeanObject,
        5839122249099470854 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6_value:
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
    m_data: [111, 110, 108, 121, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7_value:
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
    m_data: [115, 105, 122, 101, 79, 102, 95, 110, 97, 116, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9_value:
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
            l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7_value
        ) as *mut LeanObject,
        3310119546281550896 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10_value:
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
            l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11_value:
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
            l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__10_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 69, 113, 0],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14_value:
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
            l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12_value
        ) as *mut LeanObject,
        233589347272681201 as *mut LeanObject,
    ],
};
static mut l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14_value
) as *mut LeanObject;
pub static l_tacticDecreasing__trivial___closed__0_value: LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114,
        105, 118, 105, 97, 108, 0,
    ],
};
static mut l_tacticDecreasing__trivial___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__0_value) as *mut LeanObject;
pub static l_tacticDecreasing__trivial___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__0_value) as *mut LeanObject,
        5744670087858236374 as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__trivial___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__1_value) as *mut LeanObject;
pub static l_tacticDecreasing__trivial___closed__2_value: LeanStringObject<19> = LeanStringObject {
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
        100, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114, 105, 118, 105, 97, 108, 0,
    ],
};
static mut l_tacticDecreasing__trivial___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__2_value) as *mut LeanObject;
pub static l_tacticDecreasing__trivial___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__trivial___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__3_value) as *mut LeanObject;
pub static l_tacticDecreasing__trivial___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__trivial___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__4_value) as *mut LeanObject;
pub static mut l_tacticDecreasing__trivial: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 97, 99, 116, 105, 99, 95, 60, 59, 62, 95, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__0_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut LeanObject,12695378809397736991 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut LeanObject,8689124066155232629 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 105, 116, 104, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut LeanObject,3738010876686032200 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 59, 62, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 110, 101, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut LeanObject,8876691400619696497 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 109, 101, 103, 97, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0_value) as *mut LeanObject,14893461734720614794 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0_value) as *mut LeanObject,16687334436616221424 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1_value
) as *mut LeanObject;
pub static l_tacticDecreasing__trivial__pre__omega___closed__0_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114,
            105, 118, 105, 97, 108, 95, 112, 114, 101, 95, 111, 109, 101, 103, 97, 0,
        ],
    };
static mut l_tacticDecreasing__trivial__pre__omega___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__0_value)
        as *mut LeanObject;
pub static l_tacticDecreasing__trivial__pre__omega___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__0_value)
                as *mut LeanObject,
            3399267869349173528 as *mut LeanObject,
        ],
    };
static mut l_tacticDecreasing__trivial__pre__omega___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__1_value)
        as *mut LeanObject;
pub static l_tacticDecreasing__trivial__pre__omega___closed__2_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            100, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114, 105, 118, 105, 97, 108,
            95, 112, 114, 101, 95, 111, 109, 101, 103, 97, 0,
        ],
    };
static mut l_tacticDecreasing__trivial__pre__omega___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__2_value)
        as *mut LeanObject;
pub static l_tacticDecreasing__trivial__pre__omega___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_tacticDecreasing__trivial__pre__omega___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__3_value)
        as *mut LeanObject;
pub static l_tacticDecreasing__trivial__pre__omega___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_tacticDecreasing__trivial__pre__omega___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__4_value)
        as *mut LeanObject;
pub static mut l_tacticDecreasing__trivial__pre__omega: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__trivial__pre__omega___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 113, 49, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__0_value) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__0_value) as *mut LeanObject,8471002125274025202 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2_value) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2_value) as *mut LeanObject,5826123769708379594 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [78, 97, 116, 46, 115, 117, 98, 95, 115, 117, 99, 99, 95, 108, 116, 95, 115, 101, 108, 102, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4_value) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 117, 98, 95, 115, 117, 99, 99, 95, 108, 116, 95, 115, 101, 108, 102, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6_value) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__6_value) as *mut LeanObject,12340323305378594529 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [78, 97, 116, 46, 112, 114, 101, 100, 95, 108, 116, 95, 111, 102, 95, 108, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0_value) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 101, 100, 95, 108, 116, 95, 111, 102, 95, 108, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2_value) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__2_value) as *mut LeanObject,3871046354274687500 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [78, 97, 116, 46, 112, 114, 101, 100, 95, 108, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0_value) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 101, 100, 95, 108, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2_value) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__65_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__2_value) as *mut LeanObject,11419356048450776812 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__0_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 119, 105,
            116, 104, 95, 0,
        ],
    };
static mut l_tacticDecreasing__with___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__0_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__0_value) as *mut LeanObject,
        17071147086808956184 as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__with___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__1_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__2_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_tacticDecreasing__with___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__2_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__with___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__3_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__4_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            100, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 119, 105, 116, 104, 32, 0,
        ],
    };
static mut l_tacticDecreasing__with___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__4_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__4_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__with___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__5_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
            l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__6_value
        ) as *mut LeanObject,
        11103865283154438669 as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__with___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__6_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__6_value) as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__with___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__7_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__7_value) as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__with___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__8_value) as *mut LeanObject;
pub static l_tacticDecreasing__with___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__8_value) as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__with___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__9_value) as *mut LeanObject;
pub static mut l_tacticDecreasing__with__: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__with___00__closed__9_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 99, 116, 105, 99, 82, 101, 112, 101, 97, 116, 95, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__0_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__0_value) as *mut LeanObject,16592576665728214421 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 112, 101, 97, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 114, 115, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3_value) as *mut LeanObject,12551601070224435259 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__5_value) as *mut LeanObject,2214559063752339918 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [80, 114, 111, 100, 46, 76, 101, 120, 46, 114, 105, 103, 104, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [76, 101, 120, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 105, 103, 104, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value) as *mut LeanObject,15289851429949568889 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value) as *mut LeanObject,6345613489766709701 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11_value) as *mut LeanObject,8909656180514914966 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__13_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 111, 100, 46, 76, 101, 120, 46, 108, 101, 102, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 102, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__46_value) as *mut LeanObject,15289851429949568889 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value) as *mut LeanObject,6345613489766709701 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17_value) as *mut LeanObject,15868804459766548552 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__19_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [80, 83, 105, 103, 109, 97, 46, 76, 101, 120, 46, 114, 105, 103, 104, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 83, 105, 103, 109, 97, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23_value) as *mut LeanObject,16079402598994914048 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value) as *mut LeanObject,797284623638230952 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__11_value) as *mut LeanObject,5191706735699576271 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__25_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [80, 83, 105, 103, 109, 97, 46, 76, 101, 120, 46, 108, 101, 102, 116, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27_value
) as *mut LeanObject;
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28:
    *mut LeanObject = core::ptr::null_mut();
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__23_value) as *mut LeanObject,16079402598994914048 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__10_value) as *mut LeanObject,797284623638230952 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__17_value) as *mut LeanObject,2313809436473277481 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__30_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [102, 97, 105, 108, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32_value) as *mut LeanObject,59994724629665531 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__34_value) as *mut LeanObject,9232979286016572671 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36_value: LeanStringObject<262> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 262, m_capacity: 262, m_length: 261, m_data: [34, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 114, 111, 118, 101, 32, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 44, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 115, 111, 108, 117, 116, 105, 111, 110, 115, 58, 10, 32, 32, 45, 32, 85, 115, 101, 32, 96, 104, 97, 118, 101, 96, 45, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 32, 116, 111, 32, 112, 114, 111, 118, 101, 32, 116, 104, 101, 32, 114, 101, 109, 97, 105, 110, 105, 110, 103, 32, 103, 111, 97, 108, 115, 10, 32, 32, 45, 32, 85, 115, 101, 32, 96, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 95, 98, 121, 96, 32, 116, 111, 32, 115, 112, 101, 99, 105, 102, 121, 32, 97, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 119, 101, 108, 108, 45, 102, 111, 117, 110, 100, 101, 100, 32, 114, 101, 108, 97, 116, 105, 111, 110, 10, 32, 32, 45, 32, 85, 115, 101, 32, 96, 100, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 98, 121, 96, 32, 116, 111, 32, 115, 112, 101, 99, 105, 102, 121, 32, 121, 111, 117, 114, 32, 111, 119, 110, 32, 116, 97, 99, 116, 105, 99, 32, 102, 111, 114, 32, 100, 105, 115, 99, 104, 97, 114, 103, 105, 110, 103, 32, 116, 104, 105, 115, 32, 107, 105, 110, 100, 32, 111, 102, 32, 103, 111, 97, 108, 34, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36_value
) as *mut LeanObject;
pub static l_tacticDecreasing__tactic___closed__0_value: LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 97, 99,
        116, 105, 99, 0,
    ],
};
static mut l_tacticDecreasing__tactic___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__0_value) as *mut LeanObject;
pub static l_tacticDecreasing__tactic___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__0_value) as *mut LeanObject,
        8717595285447664659 as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__tactic___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__1_value) as *mut LeanObject;
pub static l_tacticDecreasing__tactic___closed__2_value: LeanStringObject<18> = LeanStringObject {
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
        100, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_tacticDecreasing__tactic___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__2_value) as *mut LeanObject;
pub static l_tacticDecreasing__tactic___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__tactic___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__3_value) as *mut LeanObject;
pub static l_tacticDecreasing__tactic___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_tacticDecreasing__tactic___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__4_value) as *mut LeanObject;
pub static mut l_tacticDecreasing__tactic: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDecreasing__tactic___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [100, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 119, 105, 116, 104, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 117, 98, 115, 116, 86, 97, 114, 115, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1_value
) as *mut LeanObject;
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__1_value) as *mut LeanObject,9452691735687745700 as *mut LeanObject] };
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 117, 98, 115, 116, 95, 118, 97, 114, 115, 0]};
static mut l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3_value
) as *mut LeanObject;
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22()
-> *mut LeanObject {
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    v___x_1204_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__21;
    v___x_1205_ = l_String_toRawSubstring_x27(v___x_1204_);
    return v___x_1205_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25()
-> *mut LeanObject {
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    v___x_1209_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__24;
    v___x_1210_ = l_String_toRawSubstring_x27(v___x_1209_);
    return v___x_1210_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27()
-> *mut LeanObject {
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_Array_mkArray0(lean_box(0));
    return v___x_1213_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32()
-> *mut LeanObject {
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    v___x_1222_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__31;
    v___x_1223_ = l_String_toRawSubstring_x27(v___x_1222_);
    return v___x_1223_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38()
-> *mut LeanObject {
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    v___x_1234_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__37;
    v___x_1235_ = l_String_toRawSubstring_x27(v___x_1234_);
    return v___x_1235_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45()
-> *mut LeanObject {
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    v___x_1250_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__44;
    v___x_1251_ = l_String_toRawSubstring_x27(v___x_1250_);
    return v___x_1251_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54()
-> *mut LeanObject {
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    v___x_1269_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__53;
    v___x_1270_ = l_String_toRawSubstring_x27(v___x_1269_);
    return v___x_1270_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59()
-> *mut LeanObject {
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    v___x_1280_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__58;
    v___x_1281_ = l_String_toRawSubstring_x27(v___x_1280_);
    return v___x_1281_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64()
-> *mut LeanObject {
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    v___x_1291_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__63;
    v___x_1292_ = l_String_toRawSubstring_x27(v___x_1291_);
    return v___x_1292_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71()
-> *mut LeanObject {
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    v___x_1305_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__70;
    v___x_1306_ = l_String_toRawSubstring_x27(v___x_1305_);
    return v___x_1306_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(
    mut v_x_1319_: *mut LeanObject,
    mut v_a_1320_: *mut LeanObject,
    mut v_a_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    v___x_1322_ = l_tacticSimp__wf___closed__1;
    v___x_1323_ = l_Lean_Syntax_isOfKind(v_x_1319_, v___x_1322_);
    if v___x_1323_ == 0 {
        let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
        v___x_1324_ = lean_box(1);
        v___x_1325_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1325_, 0, v___x_1324_);
        lean_ctor_set(v___x_1325_, 1, v_a_1321_);
        return v___x_1325_;
    } else {
        let mut v_quotContext_1326_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1327_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1329_: u8 = 0;
        let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1326_ = lean_ctor_get(v_a_1320_, 1);
        v_currMacroScope_1327_ = lean_ctor_get(v_a_1320_, 2);
        v_ref_1328_ = lean_ctor_get(v_a_1320_, 5);
        v___x_1329_ = 0;
        v___x_1330_ = l_Lean_SourceInfo_fromRef(v_ref_1328_, v___x_1329_);
        v___x_1331_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4;
        v___x_1332_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5;
        lean_inc_n(v___x_1330_, 35);
        v___x_1333_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1333_, 0, v___x_1330_);
        lean_ctor_set(v___x_1333_, 1, v___x_1332_);
        v___x_1334_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7;
        v___x_1335_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9;
        v___x_1336_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
        v___x_1337_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
        v___x_1338_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
        v___x_1339_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1339_, 0, v___x_1330_);
        lean_ctor_set(v___x_1339_, 1, v___x_1337_);
        v___x_1340_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15;
        v___x_1341_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17;
        v___x_1342_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19;
        v___x_1343_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20;
        v___x_1344_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1344_, 0, v___x_1330_);
        lean_ctor_set(v___x_1344_, 1, v___x_1343_);
        v___x_1345_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22,
        );
        v___x_1346_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23;
        lean_inc_n(v_currMacroScope_1327_, 9);
        lean_inc_n(v_quotContext_1326_, 9);
        v___x_1347_ =
            l_Lean_addMacroScope(v_quotContext_1326_, v___x_1346_, v_currMacroScope_1327_);
        v___x_1348_ = lean_box(0);
        v___x_1349_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1349_, 0, v___x_1330_);
        lean_ctor_set(v___x_1349_, 1, v___x_1345_);
        lean_ctor_set(v___x_1349_, 2, v___x_1347_);
        lean_ctor_set(v___x_1349_, 3, v___x_1348_);
        lean_inc_ref(v___x_1344_);
        v___x_1350_ = l_Lean_Syntax_node2(v___x_1330_, v___x_1342_, v___x_1344_, v___x_1349_);
        v___x_1351_ = l_Lean_Syntax_node1(v___x_1330_, v___x_1341_, v___x_1350_);
        v___x_1352_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25,
        );
        v___x_1353_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26;
        v___x_1354_ =
            l_Lean_addMacroScope(v_quotContext_1326_, v___x_1353_, v_currMacroScope_1327_);
        v___x_1355_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1355_, 0, v___x_1330_);
        lean_ctor_set(v___x_1355_, 1, v___x_1352_);
        lean_ctor_set(v___x_1355_, 2, v___x_1354_);
        lean_ctor_set(v___x_1355_, 3, v___x_1348_);
        v___x_1356_ = l_Lean_Syntax_node2(v___x_1330_, v___x_1342_, v___x_1344_, v___x_1355_);
        v___x_1357_ = l_Lean_Syntax_node1(v___x_1330_, v___x_1341_, v___x_1356_);
        v___x_1358_ = l_Lean_Syntax_node2(v___x_1330_, v___x_1336_, v___x_1351_, v___x_1357_);
        v___x_1359_ = l_Lean_Syntax_node1(v___x_1330_, v___x_1340_, v___x_1358_);
        v___x_1360_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27,
        );
        v___x_1361_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1361_, 0, v___x_1330_);
        lean_ctor_set(v___x_1361_, 1, v___x_1336_);
        lean_ctor_set(v___x_1361_, 2, v___x_1360_);
        v___x_1362_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28;
        v___x_1363_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1363_, 0, v___x_1330_);
        lean_ctor_set(v___x_1363_, 1, v___x_1362_);
        v___x_1364_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30;
        v___x_1365_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32,
        );
        v___x_1366_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33;
        v___x_1367_ =
            l_Lean_addMacroScope(v_quotContext_1326_, v___x_1366_, v_currMacroScope_1327_);
        v___x_1368_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35;
        v___x_1369_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1369_, 0, v___x_1330_);
        lean_ctor_set(v___x_1369_, 1, v___x_1365_);
        lean_ctor_set(v___x_1369_, 2, v___x_1367_);
        lean_ctor_set(v___x_1369_, 3, v___x_1368_);
        lean_inc_ref_n(v___x_1361_, 16);
        v___x_1370_ = l_Lean_Syntax_node3(
            v___x_1330_,
            v___x_1364_,
            v___x_1361_,
            v___x_1361_,
            v___x_1369_,
        );
        v___x_1371_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36;
        v___x_1372_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1372_, 0, v___x_1330_);
        lean_ctor_set(v___x_1372_, 1, v___x_1371_);
        v___x_1373_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38,
        );
        v___x_1374_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39;
        v___x_1375_ =
            l_Lean_addMacroScope(v_quotContext_1326_, v___x_1374_, v_currMacroScope_1327_);
        v___x_1376_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43;
        v___x_1377_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1377_, 0, v___x_1330_);
        lean_ctor_set(v___x_1377_, 1, v___x_1373_);
        lean_ctor_set(v___x_1377_, 2, v___x_1375_);
        lean_ctor_set(v___x_1377_, 3, v___x_1376_);
        v___x_1378_ = l_Lean_Syntax_node3(
            v___x_1330_,
            v___x_1364_,
            v___x_1361_,
            v___x_1361_,
            v___x_1377_,
        );
        v___x_1379_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45,
        );
        v___x_1380_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48;
        v___x_1381_ =
            l_Lean_addMacroScope(v_quotContext_1326_, v___x_1380_, v_currMacroScope_1327_);
        v___x_1382_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52;
        v___x_1383_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1383_, 0, v___x_1330_);
        lean_ctor_set(v___x_1383_, 1, v___x_1379_);
        lean_ctor_set(v___x_1383_, 2, v___x_1381_);
        lean_ctor_set(v___x_1383_, 3, v___x_1382_);
        v___x_1384_ = l_Lean_Syntax_node3(
            v___x_1330_,
            v___x_1364_,
            v___x_1361_,
            v___x_1361_,
            v___x_1383_,
        );
        v___x_1385_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54,
        );
        v___x_1386_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55;
        v___x_1387_ =
            l_Lean_addMacroScope(v_quotContext_1326_, v___x_1386_, v_currMacroScope_1327_);
        v___x_1388_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57;
        v___x_1389_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1389_, 0, v___x_1330_);
        lean_ctor_set(v___x_1389_, 1, v___x_1385_);
        lean_ctor_set(v___x_1389_, 2, v___x_1387_);
        lean_ctor_set(v___x_1389_, 3, v___x_1388_);
        v___x_1390_ = l_Lean_Syntax_node3(
            v___x_1330_,
            v___x_1364_,
            v___x_1361_,
            v___x_1361_,
            v___x_1389_,
        );
        v___x_1391_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59,
        );
        v___x_1392_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60;
        v___x_1393_ =
            l_Lean_addMacroScope(v_quotContext_1326_, v___x_1392_, v_currMacroScope_1327_);
        v___x_1394_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62;
        v___x_1395_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1395_, 0, v___x_1330_);
        lean_ctor_set(v___x_1395_, 1, v___x_1391_);
        lean_ctor_set(v___x_1395_, 2, v___x_1393_);
        lean_ctor_set(v___x_1395_, 3, v___x_1394_);
        v___x_1396_ = l_Lean_Syntax_node3(
            v___x_1330_,
            v___x_1364_,
            v___x_1361_,
            v___x_1361_,
            v___x_1395_,
        );
        v___x_1397_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64,
        );
        v___x_1398_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67;
        v___x_1399_ =
            l_Lean_addMacroScope(v_quotContext_1326_, v___x_1398_, v_currMacroScope_1327_);
        v___x_1400_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69;
        v___x_1401_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1401_, 0, v___x_1330_);
        lean_ctor_set(v___x_1401_, 1, v___x_1397_);
        lean_ctor_set(v___x_1401_, 2, v___x_1399_);
        lean_ctor_set(v___x_1401_, 3, v___x_1400_);
        v___x_1402_ = l_Lean_Syntax_node3(
            v___x_1330_,
            v___x_1364_,
            v___x_1361_,
            v___x_1361_,
            v___x_1401_,
        );
        v___x_1403_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71,
        );
        v___x_1404_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74;
        v___x_1405_ =
            l_Lean_addMacroScope(v_quotContext_1326_, v___x_1404_, v_currMacroScope_1327_);
        v___x_1406_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76;
        v___x_1407_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1407_, 0, v___x_1330_);
        lean_ctor_set(v___x_1407_, 1, v___x_1403_);
        lean_ctor_set(v___x_1407_, 2, v___x_1405_);
        lean_ctor_set(v___x_1407_, 3, v___x_1406_);
        v___x_1408_ = l_Lean_Syntax_node3(
            v___x_1330_,
            v___x_1364_,
            v___x_1361_,
            v___x_1361_,
            v___x_1407_,
        );
        v___x_1409_ = lean_unsigned_to_nat(13);
        v___x_1410_ = lean_mk_empty_array_with_capacity(v___x_1409_);
        v___x_1411_ = lean_array_push(v___x_1410_, v___x_1370_);
        lean_inc_ref_n(v___x_1372_, 5);
        v___x_1412_ = lean_array_push(v___x_1411_, v___x_1372_);
        v___x_1413_ = lean_array_push(v___x_1412_, v___x_1378_);
        v___x_1414_ = lean_array_push(v___x_1413_, v___x_1372_);
        v___x_1415_ = lean_array_push(v___x_1414_, v___x_1384_);
        v___x_1416_ = lean_array_push(v___x_1415_, v___x_1372_);
        v___x_1417_ = lean_array_push(v___x_1416_, v___x_1390_);
        v___x_1418_ = lean_array_push(v___x_1417_, v___x_1372_);
        v___x_1419_ = lean_array_push(v___x_1418_, v___x_1396_);
        v___x_1420_ = lean_array_push(v___x_1419_, v___x_1372_);
        v___x_1421_ = lean_array_push(v___x_1420_, v___x_1402_);
        v___x_1422_ = lean_array_push(v___x_1421_, v___x_1372_);
        v___x_1423_ = lean_array_push(v___x_1422_, v___x_1408_);
        v___x_1424_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1424_, 0, v___x_1330_);
        lean_ctor_set(v___x_1424_, 1, v___x_1336_);
        lean_ctor_set(v___x_1424_, 2, v___x_1423_);
        v___x_1425_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77;
        v___x_1426_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1426_, 0, v___x_1330_);
        lean_ctor_set(v___x_1426_, 1, v___x_1425_);
        v___x_1427_ = l_Lean_Syntax_node3(
            v___x_1330_,
            v___x_1336_,
            v___x_1363_,
            v___x_1424_,
            v___x_1426_,
        );
        v___x_1428_ = l_Lean_Syntax_node6(
            v___x_1330_,
            v___x_1338_,
            v___x_1339_,
            v___x_1359_,
            v___x_1361_,
            v___x_1361_,
            v___x_1427_,
            v___x_1361_,
        );
        v___x_1429_ = l_Lean_Syntax_node1(v___x_1330_, v___x_1336_, v___x_1428_);
        v___x_1430_ = l_Lean_Syntax_node1(v___x_1330_, v___x_1335_, v___x_1429_);
        v___x_1431_ = l_Lean_Syntax_node1(v___x_1330_, v___x_1334_, v___x_1430_);
        v___x_1432_ = l_Lean_Syntax_node2(v___x_1330_, v___x_1331_, v___x_1333_, v___x_1431_);
        v___x_1433_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1433_, 0, v___x_1432_);
        lean_ctor_set(v___x_1433_, 1, v_a_1321_);
        return v___x_1433_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___boxed(
    mut v_x_1434_: *mut LeanObject,
    mut v_a_1435_: *mut LeanObject,
    mut v_a_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1437_: *mut LeanObject = core::ptr::null_mut();
    v_res_1437_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1(
        v_x_1434_, v_a_1435_, v_a_1436_,
    );
    lean_dec_ref(v_a_1435_);
    return v_res_1437_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4()
-> *mut LeanObject {
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    v___x_1458_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__3;
    v___x_1459_ = l_String_toRawSubstring_x27(v___x_1458_);
    return v___x_1459_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8()
-> *mut LeanObject {
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1464_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__7;
    v___x_1465_ = l_String_toRawSubstring_x27(v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13()
-> *mut LeanObject {
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    v___x_1475_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__12;
    v___x_1476_ = l_String_toRawSubstring_x27(v___x_1475_);
    return v___x_1476_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(
    mut v_x_1479_: *mut LeanObject,
    mut v_a_1480_: *mut LeanObject,
    mut v_a_1481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    v___x_1482_ = l_tacticClean__wf___closed__1;
    v___x_1483_ = l_Lean_Syntax_isOfKind(v_x_1479_, v___x_1482_);
    if v___x_1483_ == 0 {
        let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
        v___x_1484_ = lean_box(1);
        v___x_1485_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1485_, 0, v___x_1484_);
        lean_ctor_set(v___x_1485_, 1, v_a_1481_);
        return v___x_1485_;
    } else {
        let mut v_quotContext_1486_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1487_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1489_: u8 = 0;
        let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1486_ = lean_ctor_get(v_a_1480_, 1);
        v_currMacroScope_1487_ = lean_ctor_get(v_a_1480_, 2);
        v_ref_1488_ = lean_ctor_get(v_a_1480_, 5);
        v___x_1489_ = 0;
        v___x_1490_ = l_Lean_SourceInfo_fromRef(v_ref_1488_, v___x_1489_);
        v___x_1491_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
        v___x_1492_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
        lean_inc_n(v___x_1490_, 40);
        v___x_1493_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1493_, 0, v___x_1490_);
        lean_ctor_set(v___x_1493_, 1, v___x_1491_);
        v___x_1494_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15;
        v___x_1495_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
        v___x_1496_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17;
        v___x_1497_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19;
        v___x_1498_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20;
        v___x_1499_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1499_, 0, v___x_1490_);
        lean_ctor_set(v___x_1499_, 1, v___x_1498_);
        v___x_1500_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__22,
        );
        v___x_1501_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__23;
        lean_inc_n(v_currMacroScope_1487_, 12);
        lean_inc_n(v_quotContext_1486_, 12);
        v___x_1502_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1501_, v_currMacroScope_1487_);
        v___x_1503_ = lean_box(0);
        v___x_1504_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1504_, 0, v___x_1490_);
        lean_ctor_set(v___x_1504_, 1, v___x_1500_);
        lean_ctor_set(v___x_1504_, 2, v___x_1502_);
        lean_ctor_set(v___x_1504_, 3, v___x_1503_);
        lean_inc_ref(v___x_1499_);
        v___x_1505_ = l_Lean_Syntax_node2(v___x_1490_, v___x_1497_, v___x_1499_, v___x_1504_);
        v___x_1506_ = l_Lean_Syntax_node1(v___x_1490_, v___x_1496_, v___x_1505_);
        v___x_1507_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__25,
        );
        v___x_1508_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__26;
        v___x_1509_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1508_, v_currMacroScope_1487_);
        v___x_1510_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1510_, 0, v___x_1490_);
        lean_ctor_set(v___x_1510_, 1, v___x_1507_);
        lean_ctor_set(v___x_1510_, 2, v___x_1509_);
        lean_ctor_set(v___x_1510_, 3, v___x_1503_);
        v___x_1511_ = l_Lean_Syntax_node2(v___x_1490_, v___x_1497_, v___x_1499_, v___x_1510_);
        v___x_1512_ = l_Lean_Syntax_node1(v___x_1490_, v___x_1496_, v___x_1511_);
        v___x_1513_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1;
        v___x_1514_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2;
        v___x_1515_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1515_, 0, v___x_1490_);
        lean_ctor_set(v___x_1515_, 1, v___x_1514_);
        v___x_1516_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4,
        );
        v___x_1517_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5;
        v___x_1518_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1517_, v_currMacroScope_1487_);
        v___x_1519_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1519_, 0, v___x_1490_);
        lean_ctor_set(v___x_1519_, 1, v___x_1516_);
        lean_ctor_set(v___x_1519_, 2, v___x_1518_);
        lean_ctor_set(v___x_1519_, 3, v___x_1503_);
        v___x_1520_ = l_Lean_Syntax_node2(v___x_1490_, v___x_1513_, v___x_1515_, v___x_1519_);
        v___x_1521_ = l_Lean_Syntax_node1(v___x_1490_, v___x_1496_, v___x_1520_);
        v___x_1522_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1495_,
            v___x_1506_,
            v___x_1512_,
            v___x_1521_,
        );
        v___x_1523_ = l_Lean_Syntax_node1(v___x_1490_, v___x_1494_, v___x_1522_);
        v___x_1524_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27,
        );
        v___x_1525_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1525_, 0, v___x_1490_);
        lean_ctor_set(v___x_1525_, 1, v___x_1495_);
        lean_ctor_set(v___x_1525_, 2, v___x_1524_);
        v___x_1526_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__6;
        v___x_1527_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1527_, 0, v___x_1490_);
        lean_ctor_set(v___x_1527_, 1, v___x_1526_);
        v___x_1528_ = l_Lean_Syntax_node1(v___x_1490_, v___x_1495_, v___x_1527_);
        v___x_1529_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__28;
        v___x_1530_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1530_, 0, v___x_1490_);
        lean_ctor_set(v___x_1530_, 1, v___x_1529_);
        v___x_1531_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__30;
        v___x_1532_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__32,
        );
        v___x_1533_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__33;
        v___x_1534_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1533_, v_currMacroScope_1487_);
        v___x_1535_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__35;
        v___x_1536_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1536_, 0, v___x_1490_);
        lean_ctor_set(v___x_1536_, 1, v___x_1532_);
        lean_ctor_set(v___x_1536_, 2, v___x_1534_);
        lean_ctor_set(v___x_1536_, 3, v___x_1535_);
        lean_inc_ref_n(v___x_1525_, 19);
        v___x_1537_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1531_,
            v___x_1525_,
            v___x_1525_,
            v___x_1536_,
        );
        v___x_1538_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__36;
        v___x_1539_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1539_, 0, v___x_1490_);
        lean_ctor_set(v___x_1539_, 1, v___x_1538_);
        v___x_1540_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__38,
        );
        v___x_1541_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__39;
        v___x_1542_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1541_, v_currMacroScope_1487_);
        v___x_1543_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__43;
        v___x_1544_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1544_, 0, v___x_1490_);
        lean_ctor_set(v___x_1544_, 1, v___x_1540_);
        lean_ctor_set(v___x_1544_, 2, v___x_1542_);
        lean_ctor_set(v___x_1544_, 3, v___x_1543_);
        v___x_1545_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1531_,
            v___x_1525_,
            v___x_1525_,
            v___x_1544_,
        );
        v___x_1546_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__45,
        );
        v___x_1547_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__48;
        v___x_1548_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1547_, v_currMacroScope_1487_);
        v___x_1549_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__52;
        v___x_1550_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1550_, 0, v___x_1490_);
        lean_ctor_set(v___x_1550_, 1, v___x_1546_);
        lean_ctor_set(v___x_1550_, 2, v___x_1548_);
        lean_ctor_set(v___x_1550_, 3, v___x_1549_);
        v___x_1551_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1531_,
            v___x_1525_,
            v___x_1525_,
            v___x_1550_,
        );
        v___x_1552_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__54,
        );
        v___x_1553_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__55;
        v___x_1554_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1553_, v_currMacroScope_1487_);
        v___x_1555_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__57;
        v___x_1556_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1556_, 0, v___x_1490_);
        lean_ctor_set(v___x_1556_, 1, v___x_1552_);
        lean_ctor_set(v___x_1556_, 2, v___x_1554_);
        lean_ctor_set(v___x_1556_, 3, v___x_1555_);
        v___x_1557_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1531_,
            v___x_1525_,
            v___x_1525_,
            v___x_1556_,
        );
        v___x_1558_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__59,
        );
        v___x_1559_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__60;
        v___x_1560_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1559_, v_currMacroScope_1487_);
        v___x_1561_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__62;
        v___x_1562_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1562_, 0, v___x_1490_);
        lean_ctor_set(v___x_1562_, 1, v___x_1558_);
        lean_ctor_set(v___x_1562_, 2, v___x_1560_);
        lean_ctor_set(v___x_1562_, 3, v___x_1561_);
        v___x_1563_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1531_,
            v___x_1525_,
            v___x_1525_,
            v___x_1562_,
        );
        v___x_1564_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__64,
        );
        v___x_1565_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__67;
        v___x_1566_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1565_, v_currMacroScope_1487_);
        v___x_1567_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__69;
        v___x_1568_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1568_, 0, v___x_1490_);
        lean_ctor_set(v___x_1568_, 1, v___x_1564_);
        lean_ctor_set(v___x_1568_, 2, v___x_1566_);
        lean_ctor_set(v___x_1568_, 3, v___x_1567_);
        v___x_1569_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1531_,
            v___x_1525_,
            v___x_1525_,
            v___x_1568_,
        );
        v___x_1570_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__71,
        );
        v___x_1571_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__74;
        v___x_1572_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1571_, v_currMacroScope_1487_);
        v___x_1573_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__76;
        v___x_1574_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1574_, 0, v___x_1490_);
        lean_ctor_set(v___x_1574_, 1, v___x_1570_);
        lean_ctor_set(v___x_1574_, 2, v___x_1572_);
        lean_ctor_set(v___x_1574_, 3, v___x_1573_);
        v___x_1575_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1531_,
            v___x_1525_,
            v___x_1525_,
            v___x_1574_,
        );
        v___x_1576_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__8,
        );
        v___x_1577_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__9;
        v___x_1578_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1577_, v_currMacroScope_1487_);
        v___x_1579_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__11;
        v___x_1580_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1580_, 0, v___x_1490_);
        lean_ctor_set(v___x_1580_, 1, v___x_1576_);
        lean_ctor_set(v___x_1580_, 2, v___x_1578_);
        lean_ctor_set(v___x_1580_, 3, v___x_1579_);
        v___x_1581_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1531_,
            v___x_1525_,
            v___x_1525_,
            v___x_1580_,
        );
        v___x_1582_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__13,
        );
        v___x_1583_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__14;
        v___x_1584_ =
            l_Lean_addMacroScope(v_quotContext_1486_, v___x_1583_, v_currMacroScope_1487_);
        v___x_1585_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1585_, 0, v___x_1490_);
        lean_ctor_set(v___x_1585_, 1, v___x_1582_);
        lean_ctor_set(v___x_1585_, 2, v___x_1584_);
        lean_ctor_set(v___x_1585_, 3, v___x_1503_);
        v___x_1586_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1531_,
            v___x_1525_,
            v___x_1525_,
            v___x_1585_,
        );
        v___x_1587_ = lean_unsigned_to_nat(17);
        v___x_1588_ = lean_mk_empty_array_with_capacity(v___x_1587_);
        v___x_1589_ = lean_array_push(v___x_1588_, v___x_1537_);
        lean_inc_ref_n(v___x_1539_, 7);
        v___x_1590_ = lean_array_push(v___x_1589_, v___x_1539_);
        v___x_1591_ = lean_array_push(v___x_1590_, v___x_1545_);
        v___x_1592_ = lean_array_push(v___x_1591_, v___x_1539_);
        v___x_1593_ = lean_array_push(v___x_1592_, v___x_1551_);
        v___x_1594_ = lean_array_push(v___x_1593_, v___x_1539_);
        v___x_1595_ = lean_array_push(v___x_1594_, v___x_1557_);
        v___x_1596_ = lean_array_push(v___x_1595_, v___x_1539_);
        v___x_1597_ = lean_array_push(v___x_1596_, v___x_1563_);
        v___x_1598_ = lean_array_push(v___x_1597_, v___x_1539_);
        v___x_1599_ = lean_array_push(v___x_1598_, v___x_1569_);
        v___x_1600_ = lean_array_push(v___x_1599_, v___x_1539_);
        v___x_1601_ = lean_array_push(v___x_1600_, v___x_1575_);
        v___x_1602_ = lean_array_push(v___x_1601_, v___x_1539_);
        v___x_1603_ = lean_array_push(v___x_1602_, v___x_1581_);
        v___x_1604_ = lean_array_push(v___x_1603_, v___x_1539_);
        v___x_1605_ = lean_array_push(v___x_1604_, v___x_1586_);
        v___x_1606_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1606_, 0, v___x_1490_);
        lean_ctor_set(v___x_1606_, 1, v___x_1495_);
        lean_ctor_set(v___x_1606_, 2, v___x_1605_);
        v___x_1607_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__77;
        v___x_1608_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1608_, 0, v___x_1490_);
        lean_ctor_set(v___x_1608_, 1, v___x_1607_);
        v___x_1609_ = l_Lean_Syntax_node3(
            v___x_1490_,
            v___x_1495_,
            v___x_1530_,
            v___x_1606_,
            v___x_1608_,
        );
        v___x_1610_ = l_Lean_Syntax_node6(
            v___x_1490_,
            v___x_1492_,
            v___x_1493_,
            v___x_1523_,
            v___x_1525_,
            v___x_1528_,
            v___x_1609_,
            v___x_1525_,
        );
        v___x_1611_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1611_, 0, v___x_1610_);
        lean_ctor_set(v___x_1611_, 1, v_a_1481_);
        return v___x_1611_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___boxed(
    mut v_x_1612_: *mut LeanObject,
    mut v_a_1613_: *mut LeanObject,
    mut v_a_1614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1615_: *mut LeanObject = core::ptr::null_mut();
    v_res_1615_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1(
        v_x_1612_, v_a_1613_, v_a_1614_,
    );
    lean_dec_ref(v_a_1613_);
    return v_res_1615_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6()
-> *mut LeanObject {
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    v___x_1642_ =
        l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__5;
    v___x_1643_ = l_String_toRawSubstring_x27(v___x_1642_);
    return v___x_1643_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(
    mut v_x_1654_: *mut LeanObject,
    mut v_a_1655_: *mut LeanObject,
    mut v_a_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u8 = 0;
    v___x_1657_ = l_tacticDecreasing__trivial___closed__1;
    v___x_1658_ = l_Lean_Syntax_isOfKind(v_x_1654_, v___x_1657_);
    if v___x_1658_ == 0 {
        let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
        v___x_1659_ = lean_box(1);
        v___x_1660_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1660_, 0, v___x_1659_);
        lean_ctor_set(v___x_1660_, 1, v_a_1656_);
        return v___x_1660_;
    } else {
        let mut v_quotContext_1661_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1662_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1664_: u8 = 0;
        let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1661_ = lean_ctor_get(v_a_1655_, 1);
        v_currMacroScope_1662_ = lean_ctor_get(v_a_1655_, 2);
        v_ref_1663_ = lean_ctor_get(v_a_1655_, 5);
        v___x_1664_ = 0;
        v___x_1665_ = l_Lean_SourceInfo_fromRef(v_ref_1663_, v___x_1664_);
        v___x_1666_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__1;
        v___x_1667_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3;
        v___x_1668_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4;
        lean_inc_n(v___x_1665_, 22);
        v___x_1669_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1669_, 0, v___x_1665_);
        lean_ctor_set(v___x_1669_, 1, v___x_1668_);
        v___x_1670_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7;
        v___x_1671_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9;
        v___x_1672_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
        v___x_1673_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
        v___x_1674_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
        v___x_1675_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1675_, 0, v___x_1665_);
        lean_ctor_set(v___x_1675_, 1, v___x_1673_);
        v___x_1676_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15;
        v___x_1677_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__17;
        v___x_1678_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__19;
        v___x_1679_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__20;
        v___x_1680_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1680_, 0, v___x_1665_);
        lean_ctor_set(v___x_1680_, 1, v___x_1679_);
        v___x_1681_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6), core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6_once), _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__6);
        v___x_1682_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__7;
        lean_inc_n(v_currMacroScope_1662_, 2);
        lean_inc_n(v_quotContext_1661_, 2);
        v___x_1683_ =
            l_Lean_addMacroScope(v_quotContext_1661_, v___x_1682_, v_currMacroScope_1662_);
        v___x_1684_ = lean_box(0);
        v___x_1685_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1685_, 0, v___x_1665_);
        lean_ctor_set(v___x_1685_, 1, v___x_1681_);
        lean_ctor_set(v___x_1685_, 2, v___x_1683_);
        lean_ctor_set(v___x_1685_, 3, v___x_1684_);
        v___x_1686_ = l_Lean_Syntax_node2(v___x_1665_, v___x_1678_, v___x_1680_, v___x_1685_);
        v___x_1687_ = l_Lean_Syntax_node1(v___x_1665_, v___x_1677_, v___x_1686_);
        v___x_1688_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__1;
        v___x_1689_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__2;
        v___x_1690_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1690_, 0, v___x_1665_);
        lean_ctor_set(v___x_1690_, 1, v___x_1689_);
        v___x_1691_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__4,
        );
        v___x_1692_ = l___aux__Init__WFTactics______macroRules__tacticClean__wf__1___closed__5;
        v___x_1693_ =
            l_Lean_addMacroScope(v_quotContext_1661_, v___x_1692_, v_currMacroScope_1662_);
        v___x_1694_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1694_, 0, v___x_1665_);
        lean_ctor_set(v___x_1694_, 1, v___x_1691_);
        lean_ctor_set(v___x_1694_, 2, v___x_1693_);
        lean_ctor_set(v___x_1694_, 3, v___x_1684_);
        v___x_1695_ = l_Lean_Syntax_node2(v___x_1665_, v___x_1688_, v___x_1690_, v___x_1694_);
        v___x_1696_ = l_Lean_Syntax_node1(v___x_1665_, v___x_1677_, v___x_1695_);
        v___x_1697_ = l_Lean_Syntax_node2(v___x_1665_, v___x_1672_, v___x_1687_, v___x_1696_);
        v___x_1698_ = l_Lean_Syntax_node1(v___x_1665_, v___x_1676_, v___x_1697_);
        v___x_1699_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27,
        );
        v___x_1700_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1700_, 0, v___x_1665_);
        lean_ctor_set(v___x_1700_, 1, v___x_1672_);
        lean_ctor_set(v___x_1700_, 2, v___x_1699_);
        lean_inc_ref_n(v___x_1700_, 3);
        v___x_1701_ = l_Lean_Syntax_node6(
            v___x_1665_,
            v___x_1674_,
            v___x_1675_,
            v___x_1698_,
            v___x_1700_,
            v___x_1700_,
            v___x_1700_,
            v___x_1700_,
        );
        v___x_1702_ = l_Lean_Syntax_node1(v___x_1665_, v___x_1672_, v___x_1701_);
        v___x_1703_ = l_Lean_Syntax_node1(v___x_1665_, v___x_1671_, v___x_1702_);
        v___x_1704_ = l_Lean_Syntax_node1(v___x_1665_, v___x_1670_, v___x_1703_);
        v___x_1705_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_1706_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1706_, 0, v___x_1665_);
        lean_ctor_set(v___x_1706_, 1, v___x_1705_);
        v___x_1707_ = l_Lean_Syntax_node3(
            v___x_1665_,
            v___x_1667_,
            v___x_1669_,
            v___x_1704_,
            v___x_1706_,
        );
        v___x_1708_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__9;
        v___x_1709_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1709_, 0, v___x_1665_);
        lean_ctor_set(v___x_1709_, 1, v___x_1708_);
        v___x_1710_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10;
        v___x_1711_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_1712_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1712_, 0, v___x_1665_);
        lean_ctor_set(v___x_1712_, 1, v___x_1710_);
        v___x_1713_ = l_Lean_Syntax_node1(v___x_1665_, v___x_1711_, v___x_1712_);
        v___x_1714_ = l_Lean_Syntax_node3(
            v___x_1665_,
            v___x_1666_,
            v___x_1707_,
            v___x_1709_,
            v___x_1713_,
        );
        v___x_1715_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1715_, 0, v___x_1714_);
        lean_ctor_set(v___x_1715_, 1, v_a_1656_);
        return v___x_1715_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___boxed(
    mut v_x_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
    mut v_a_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1719_: *mut LeanObject = core::ptr::null_mut();
    v_res_1719_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1(
        v_x_1716_, v_a_1717_, v_a_1718_,
    );
    lean_dec_ref(v_a_1717_);
    return v_res_1719_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(
    mut v_x_1726_: *mut LeanObject,
    mut v_a_1727_: *mut LeanObject,
    mut v_a_1728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: u8 = 0;
    v___x_1729_ = l_tacticDecreasing__trivial___closed__1;
    v___x_1730_ = l_Lean_Syntax_isOfKind(v_x_1726_, v___x_1729_);
    if v___x_1730_ == 0 {
        let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
        v___x_1731_ = lean_box(1);
        v___x_1732_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1732_, 0, v___x_1731_);
        lean_ctor_set(v___x_1732_, 1, v_a_1728_);
        return v___x_1732_;
    } else {
        let mut v_ref_1733_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1734_: u8 = 0;
        let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
        v_ref_1733_ = lean_ctor_get(v_a_1727_, 5);
        v___x_1734_ = 0;
        v___x_1735_ = l_Lean_SourceInfo_fromRef(v_ref_1733_, v___x_1734_);
        v___x_1736_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__0;
        v___x_1737_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___closed__1;
        lean_inc_n(v___x_1735_, 3);
        v___x_1738_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1738_, 0, v___x_1735_);
        lean_ctor_set(v___x_1738_, 1, v___x_1736_);
        v___x_1739_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15;
        v___x_1740_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
        v___x_1741_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27,
        );
        v___x_1742_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1742_, 0, v___x_1735_);
        lean_ctor_set(v___x_1742_, 1, v___x_1740_);
        lean_ctor_set(v___x_1742_, 2, v___x_1741_);
        v___x_1743_ = l_Lean_Syntax_node1(v___x_1735_, v___x_1739_, v___x_1742_);
        v___x_1744_ = l_Lean_Syntax_node2(v___x_1735_, v___x_1737_, v___x_1738_, v___x_1743_);
        v___x_1745_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1745_, 0, v___x_1744_);
        lean_ctor_set(v___x_1745_, 1, v_a_1728_);
        return v___x_1745_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2___boxed(
    mut v_x_1746_: *mut LeanObject,
    mut v_a_1747_: *mut LeanObject,
    mut v_a_1748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1749_: *mut LeanObject = core::ptr::null_mut();
    v_res_1749_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__2(
        v_x_1746_, v_a_1747_, v_a_1748_,
    );
    lean_dec_ref(v_a_1747_);
    return v_res_1749_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(
    mut v_x_1756_: *mut LeanObject,
    mut v_a_1757_: *mut LeanObject,
    mut v_a_1758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u8 = 0;
    v___x_1759_ = l_tacticDecreasing__trivial___closed__1;
    v___x_1760_ = l_Lean_Syntax_isOfKind(v_x_1756_, v___x_1759_);
    if v___x_1760_ == 0 {
        let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
        v___x_1761_ = lean_box(1);
        v___x_1762_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1762_, 0, v___x_1761_);
        lean_ctor_set(v___x_1762_, 1, v_a_1758_);
        return v___x_1762_;
    } else {
        let mut v_ref_1763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: u8 = 0;
        let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
        v_ref_1763_ = lean_ctor_get(v_a_1757_, 5);
        v___x_1764_ = 0;
        v___x_1765_ = l_Lean_SourceInfo_fromRef(v_ref_1763_, v___x_1764_);
        v___x_1766_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0;
        v___x_1767_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
        lean_inc(v___x_1765_);
        v___x_1768_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1768_, 0, v___x_1765_);
        lean_ctor_set(v___x_1768_, 1, v___x_1766_);
        v___x_1769_ = l_Lean_Syntax_node1(v___x_1765_, v___x_1767_, v___x_1768_);
        v___x_1770_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1770_, 0, v___x_1769_);
        lean_ctor_set(v___x_1770_, 1, v_a_1758_);
        return v___x_1770_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___boxed(
    mut v_x_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
    mut v_a_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1774_: *mut LeanObject = core::ptr::null_mut();
    v_res_1774_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3(
        v_x_1771_, v_a_1772_, v_a_1773_,
    );
    lean_dec_ref(v_a_1772_);
    return v_res_1774_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5()
-> *mut LeanObject {
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    v___x_1800_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__4;
    v___x_1801_ = l_String_toRawSubstring_x27(v___x_1800_);
    return v___x_1801_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(
    mut v_x_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    v___x_1816_ = l_tacticDecreasing__trivial__pre__omega___closed__1;
    v___x_1817_ = l_Lean_Syntax_isOfKind(v_x_1813_, v___x_1816_);
    if v___x_1817_ == 0 {
        let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
        v___x_1818_ = lean_box(1);
        v___x_1819_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1819_, 0, v___x_1818_);
        lean_ctor_set(v___x_1819_, 1, v_a_1815_);
        return v___x_1819_;
    } else {
        let mut v_quotContext_1820_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1821_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1823_: u8 = 0;
        let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1820_ = lean_ctor_get(v_a_1814_, 1);
        v_currMacroScope_1821_ = lean_ctor_get(v_a_1814_, 2);
        v_ref_1822_ = lean_ctor_get(v_a_1814_, 5);
        v___x_1823_ = 0;
        v___x_1824_ = l_Lean_SourceInfo_fromRef(v_ref_1822_, v___x_1823_);
        v___x_1825_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1;
        v___x_1826_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
        v___x_1827_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2;
        v___x_1828_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
        lean_inc_n(v___x_1824_, 7);
        v___x_1829_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1829_, 0, v___x_1824_);
        lean_ctor_set(v___x_1829_, 1, v___x_1827_);
        v___x_1830_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5), core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5_once), _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__5);
        v___x_1831_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__7;
        lean_inc(v_currMacroScope_1821_);
        lean_inc(v_quotContext_1820_);
        v___x_1832_ =
            l_Lean_addMacroScope(v_quotContext_1820_, v___x_1831_, v_currMacroScope_1821_);
        v___x_1833_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__9;
        v___x_1834_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1834_, 0, v___x_1824_);
        lean_ctor_set(v___x_1834_, 1, v___x_1830_);
        lean_ctor_set(v___x_1834_, 2, v___x_1832_);
        lean_ctor_set(v___x_1834_, 3, v___x_1833_);
        v___x_1835_ = l_Lean_Syntax_node2(v___x_1824_, v___x_1828_, v___x_1829_, v___x_1834_);
        v___x_1836_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10;
        v___x_1837_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1837_, 0, v___x_1824_);
        lean_ctor_set(v___x_1837_, 1, v___x_1836_);
        v___x_1838_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0;
        v___x_1839_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
        v___x_1840_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1840_, 0, v___x_1824_);
        lean_ctor_set(v___x_1840_, 1, v___x_1838_);
        v___x_1841_ = l_Lean_Syntax_node1(v___x_1824_, v___x_1839_, v___x_1840_);
        v___x_1842_ = l_Lean_Syntax_node3(
            v___x_1824_,
            v___x_1826_,
            v___x_1835_,
            v___x_1837_,
            v___x_1841_,
        );
        v___x_1843_ = l_Lean_Syntax_node1(v___x_1824_, v___x_1825_, v___x_1842_);
        v___x_1844_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1844_, 0, v___x_1843_);
        lean_ctor_set(v___x_1844_, 1, v_a_1815_);
        return v___x_1844_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___boxed(
    mut v_x_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
    mut v_a_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1848_: *mut LeanObject = core::ptr::null_mut();
    v_res_1848_ =
        l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1(
            v_x_1845_, v_a_1846_, v_a_1847_,
        );
    lean_dec_ref(v_a_1846_);
    return v_res_1848_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1()
-> *mut LeanObject {
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1850_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__0;
    v___x_1851_ = l_String_toRawSubstring_x27(v___x_1850_);
    return v___x_1851_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(
    mut v_x_1862_: *mut LeanObject,
    mut v_a_1863_: *mut LeanObject,
    mut v_a_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: u8 = 0;
    v___x_1865_ = l_tacticDecreasing__trivial__pre__omega___closed__1;
    v___x_1866_ = l_Lean_Syntax_isOfKind(v_x_1862_, v___x_1865_);
    if v___x_1866_ == 0 {
        let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
        v___x_1867_ = lean_box(1);
        v___x_1868_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1868_, 0, v___x_1867_);
        lean_ctor_set(v___x_1868_, 1, v_a_1864_);
        return v___x_1868_;
    } else {
        let mut v_quotContext_1869_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1870_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1872_: u8 = 0;
        let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1869_ = lean_ctor_get(v_a_1863_, 1);
        v_currMacroScope_1870_ = lean_ctor_get(v_a_1863_, 2);
        v_ref_1871_ = lean_ctor_get(v_a_1863_, 5);
        v___x_1872_ = 0;
        v___x_1873_ = l_Lean_SourceInfo_fromRef(v_ref_1871_, v___x_1872_);
        v___x_1874_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1;
        v___x_1875_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
        v___x_1876_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2;
        v___x_1877_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
        lean_inc_n(v___x_1873_, 7);
        v___x_1878_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1878_, 0, v___x_1873_);
        lean_ctor_set(v___x_1878_, 1, v___x_1876_);
        v___x_1879_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1), core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1_once), _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__1);
        v___x_1880_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__3;
        lean_inc(v_currMacroScope_1870_);
        lean_inc(v_quotContext_1869_);
        v___x_1881_ =
            l_Lean_addMacroScope(v_quotContext_1869_, v___x_1880_, v_currMacroScope_1870_);
        v___x_1882_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___closed__5;
        v___x_1883_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1883_, 0, v___x_1873_);
        lean_ctor_set(v___x_1883_, 1, v___x_1879_);
        lean_ctor_set(v___x_1883_, 2, v___x_1881_);
        lean_ctor_set(v___x_1883_, 3, v___x_1882_);
        v___x_1884_ = l_Lean_Syntax_node2(v___x_1873_, v___x_1877_, v___x_1878_, v___x_1883_);
        v___x_1885_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10;
        v___x_1886_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1886_, 0, v___x_1873_);
        lean_ctor_set(v___x_1886_, 1, v___x_1885_);
        v___x_1887_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0;
        v___x_1888_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
        v___x_1889_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1889_, 0, v___x_1873_);
        lean_ctor_set(v___x_1889_, 1, v___x_1887_);
        v___x_1890_ = l_Lean_Syntax_node1(v___x_1873_, v___x_1888_, v___x_1889_);
        v___x_1891_ = l_Lean_Syntax_node3(
            v___x_1873_,
            v___x_1875_,
            v___x_1884_,
            v___x_1886_,
            v___x_1890_,
        );
        v___x_1892_ = l_Lean_Syntax_node1(v___x_1873_, v___x_1874_, v___x_1891_);
        v___x_1893_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1893_, 0, v___x_1892_);
        lean_ctor_set(v___x_1893_, 1, v_a_1864_);
        return v___x_1893_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2___boxed(
    mut v_x_1894_: *mut LeanObject,
    mut v_a_1895_: *mut LeanObject,
    mut v_a_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_res_1897_ =
        l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__2(
            v_x_1894_, v_a_1895_, v_a_1896_,
        );
    lean_dec_ref(v_a_1895_);
    return v_res_1897_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1()
-> *mut LeanObject {
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    v___x_1899_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__0;
    v___x_1900_ = l_String_toRawSubstring_x27(v___x_1899_);
    return v___x_1900_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(
    mut v_x_1911_: *mut LeanObject,
    mut v_a_1912_: *mut LeanObject,
    mut v_a_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    v___x_1914_ = l_tacticDecreasing__trivial__pre__omega___closed__1;
    v___x_1915_ = l_Lean_Syntax_isOfKind(v_x_1911_, v___x_1914_);
    if v___x_1915_ == 0 {
        let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
        v___x_1916_ = lean_box(1);
        v___x_1917_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1917_, 0, v___x_1916_);
        lean_ctor_set(v___x_1917_, 1, v_a_1913_);
        return v___x_1917_;
    } else {
        let mut v_quotContext_1918_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1919_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: u8 = 0;
        let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1918_ = lean_ctor_get(v_a_1912_, 1);
        v_currMacroScope_1919_ = lean_ctor_get(v_a_1912_, 2);
        v_ref_1920_ = lean_ctor_get(v_a_1912_, 5);
        v___x_1921_ = 0;
        v___x_1922_ = l_Lean_SourceInfo_fromRef(v_ref_1920_, v___x_1921_);
        v___x_1923_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__1;
        v___x_1924_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
        v___x_1925_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2;
        v___x_1926_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
        lean_inc_n(v___x_1922_, 7);
        v___x_1927_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1927_, 0, v___x_1922_);
        lean_ctor_set(v___x_1927_, 1, v___x_1925_);
        v___x_1928_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1), core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1_once), _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__1);
        v___x_1929_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__3;
        lean_inc(v_currMacroScope_1919_);
        lean_inc(v_quotContext_1918_);
        v___x_1930_ =
            l_Lean_addMacroScope(v_quotContext_1918_, v___x_1929_, v_currMacroScope_1919_);
        v___x_1931_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___closed__5;
        v___x_1932_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1932_, 0, v___x_1922_);
        lean_ctor_set(v___x_1932_, 1, v___x_1928_);
        lean_ctor_set(v___x_1932_, 2, v___x_1930_);
        lean_ctor_set(v___x_1932_, 3, v___x_1931_);
        v___x_1933_ = l_Lean_Syntax_node2(v___x_1922_, v___x_1926_, v___x_1927_, v___x_1932_);
        v___x_1934_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10;
        v___x_1935_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1935_, 0, v___x_1922_);
        lean_ctor_set(v___x_1935_, 1, v___x_1934_);
        v___x_1936_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__0;
        v___x_1937_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__3___closed__1;
        v___x_1938_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1938_, 0, v___x_1922_);
        lean_ctor_set(v___x_1938_, 1, v___x_1936_);
        v___x_1939_ = l_Lean_Syntax_node1(v___x_1922_, v___x_1937_, v___x_1938_);
        v___x_1940_ = l_Lean_Syntax_node3(
            v___x_1922_,
            v___x_1924_,
            v___x_1933_,
            v___x_1935_,
            v___x_1939_,
        );
        v___x_1941_ = l_Lean_Syntax_node1(v___x_1922_, v___x_1923_, v___x_1940_);
        v___x_1942_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1942_, 0, v___x_1941_);
        lean_ctor_set(v___x_1942_, 1, v_a_1913_);
        return v___x_1942_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3___boxed(
    mut v_x_1943_: *mut LeanObject,
    mut v_a_1944_: *mut LeanObject,
    mut v_a_1945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1946_: *mut LeanObject = core::ptr::null_mut();
    v_res_1946_ =
        l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__3(
            v_x_1943_, v_a_1944_, v_a_1945_,
        );
    lean_dec_ref(v_a_1944_);
    return v_res_1946_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9()
-> *mut LeanObject {
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    v___x_1988_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__8;
    v___x_1989_ = l_String_toRawSubstring_x27(v___x_1988_);
    return v___x_1989_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16()
-> *mut LeanObject {
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    v___x_2003_ =
        l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__15;
    v___x_2004_ = l_String_toRawSubstring_x27(v___x_2003_);
    return v___x_2004_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22()
-> *mut LeanObject {
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    v___x_2017_ =
        l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__21;
    v___x_2018_ = l_String_toRawSubstring_x27(v___x_2017_);
    return v___x_2018_;
}
pub unsafe fn _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28()
-> *mut LeanObject {
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    v___x_2031_ =
        l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__27;
    v___x_2032_ = l_String_toRawSubstring_x27(v___x_2031_);
    return v___x_2032_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(
    mut v_x_2053_: *mut LeanObject,
    mut v_a_2054_: *mut LeanObject,
    mut v_a_2055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    v___x_2056_ = l_tacticDecreasing__with___00__closed__1;
    lean_inc(v_x_2053_);
    v___x_2057_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2056_);
    if v___x_2057_ == 0 {
        let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2053_);
        v___x_2058_ = lean_box(1);
        v___x_2059_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2059_, 0, v___x_2058_);
        lean_ctor_set(v___x_2059_, 1, v_a_2055_);
        return v___x_2059_;
    } else {
        let mut v_quotContext_2060_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2061_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2066_: u8 = 0;
        let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2060_ = lean_ctor_get(v_a_2054_, 1);
        v_currMacroScope_2061_ = lean_ctor_get(v_a_2054_, 2);
        v_ref_2062_ = lean_ctor_get(v_a_2054_, 5);
        v___x_2063_ = lean_unsigned_to_nat(1);
        v___x_2064_ = l_Lean_Syntax_getArg(v_x_2053_, v___x_2063_);
        lean_dec(v_x_2053_);
        v___x_2065_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7;
        v___x_2066_ = 0;
        v___x_2067_ = l_Lean_SourceInfo_fromRef(v_ref_2062_, v___x_2066_);
        v___x_2068_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__3;
        v___x_2069_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__4;
        lean_inc_n(v___x_2067_, 82);
        v___x_2070_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2070_, 0, v___x_2067_);
        lean_ctor_set(v___x_2070_, 1, v___x_2069_);
        v___x_2071_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9;
        v___x_2072_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
        v___x_2073_ = l_tacticClean__wf___closed__1;
        v___x_2074_ = l_tacticClean__wf___closed__2;
        v___x_2075_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2075_, 0, v___x_2067_);
        lean_ctor_set(v___x_2075_, 1, v___x_2074_);
        v___x_2076_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2073_, v___x_2075_);
        v___x_2077_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27_once
            ),
            _init_l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__27,
        );
        v___x_2078_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2078_, 0, v___x_2067_);
        lean_ctor_set(v___x_2078_, 1, v___x_2072_);
        lean_ctor_set(v___x_2078_, 2, v___x_2077_);
        v___x_2079_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__4;
        v___x_2080_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__5;
        v___x_2081_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2081_, 0, v___x_2067_);
        lean_ctor_set(v___x_2081_, 1, v___x_2080_);
        v___x_2082_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__12;
        v___x_2083_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__13;
        v___x_2084_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2084_, 0, v___x_2067_);
        lean_ctor_set(v___x_2084_, 1, v___x_2082_);
        v___x_2085_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__15;
        lean_inc_ref_n(v___x_2078_, 8);
        v___x_2086_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2085_, v___x_2078_);
        v___x_2087_ = l_Lean_Syntax_node6(
            v___x_2067_,
            v___x_2083_,
            v___x_2084_,
            v___x_2086_,
            v___x_2078_,
            v___x_2078_,
            v___x_2078_,
            v___x_2078_,
        );
        v___x_2088_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2087_);
        v___x_2089_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2088_);
        v___x_2090_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2089_);
        v___x_2091_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2079_, v___x_2081_, v___x_2090_);
        v___x_2092_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__1;
        v___x_2093_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__2;
        v___x_2094_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2094_, 0, v___x_2067_);
        lean_ctor_set(v___x_2094_, 1, v___x_2093_);
        v___x_2095_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3;
        v___x_2096_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4;
        v___x_2097_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2097_, 0, v___x_2067_);
        lean_ctor_set(v___x_2097_, 1, v___x_2095_);
        v___x_2098_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6;
        v___x_2099_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7;
        v___x_2100_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2100_, 0, v___x_2067_);
        lean_ctor_set(v___x_2100_, 1, v___x_2099_);
        v___x_2101_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__2;
        v___x_2102_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__3;
        v___x_2103_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2103_, 0, v___x_2067_);
        lean_ctor_set(v___x_2103_, 1, v___x_2101_);
        v___x_2104_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9), core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9_once), _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__9);
        v___x_2105_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__12;
        lean_inc_n(v_currMacroScope_2061_, 4);
        lean_inc_n(v_quotContext_2060_, 4);
        v___x_2106_ =
            l_Lean_addMacroScope(v_quotContext_2060_, v___x_2105_, v_currMacroScope_2061_);
        v___x_2107_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__14;
        v___x_2108_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2108_, 0, v___x_2067_);
        lean_ctor_set(v___x_2108_, 1, v___x_2104_);
        lean_ctor_set(v___x_2108_, 2, v___x_2106_);
        lean_ctor_set(v___x_2108_, 3, v___x_2107_);
        lean_inc_ref_n(v___x_2103_, 3);
        v___x_2109_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2102_, v___x_2103_, v___x_2108_);
        v___x_2110_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2109_);
        v___x_2111_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2110_);
        v___x_2112_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2111_);
        lean_inc_ref_n(v___x_2100_, 6);
        v___x_2113_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2098_, v___x_2100_, v___x_2112_);
        v___x_2114_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16), core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16_once), _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__16);
        v___x_2115_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__18;
        v___x_2116_ =
            l_Lean_addMacroScope(v_quotContext_2060_, v___x_2115_, v_currMacroScope_2061_);
        v___x_2117_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__20;
        v___x_2118_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2118_, 0, v___x_2067_);
        lean_ctor_set(v___x_2118_, 1, v___x_2114_);
        lean_ctor_set(v___x_2118_, 2, v___x_2116_);
        lean_ctor_set(v___x_2118_, 3, v___x_2117_);
        v___x_2119_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2102_, v___x_2103_, v___x_2118_);
        v___x_2120_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2119_);
        v___x_2121_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2120_);
        v___x_2122_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2121_);
        v___x_2123_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2098_, v___x_2100_, v___x_2122_);
        v___x_2124_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2072_, v___x_2113_, v___x_2123_);
        lean_inc_ref_n(v___x_2097_, 2);
        v___x_2125_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2096_, v___x_2097_, v___x_2124_);
        v___x_2126_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2125_);
        v___x_2127_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2126_);
        v___x_2128_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2127_);
        v___x_2129_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_2130_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2130_, 0, v___x_2067_);
        lean_ctor_set(v___x_2130_, 1, v___x_2129_);
        lean_inc_ref_n(v___x_2130_, 2);
        lean_inc_ref_n(v___x_2070_, 2);
        v___x_2131_ = l_Lean_Syntax_node3(
            v___x_2067_,
            v___x_2068_,
            v___x_2070_,
            v___x_2128_,
            v___x_2130_,
        );
        v___x_2132_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2131_);
        v___x_2133_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2132_);
        v___x_2134_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2133_);
        lean_inc_ref(v___x_2094_);
        v___x_2135_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2092_, v___x_2094_, v___x_2134_);
        v___x_2136_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22), core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22_once), _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__22);
        v___x_2137_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__24;
        v___x_2138_ =
            l_Lean_addMacroScope(v_quotContext_2060_, v___x_2137_, v_currMacroScope_2061_);
        v___x_2139_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__26;
        v___x_2140_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2140_, 0, v___x_2067_);
        lean_ctor_set(v___x_2140_, 1, v___x_2136_);
        lean_ctor_set(v___x_2140_, 2, v___x_2138_);
        lean_ctor_set(v___x_2140_, 3, v___x_2139_);
        v___x_2141_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2102_, v___x_2103_, v___x_2140_);
        v___x_2142_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2141_);
        v___x_2143_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2142_);
        v___x_2144_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2143_);
        v___x_2145_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2098_, v___x_2100_, v___x_2144_);
        v___x_2146_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28), core::ptr::addr_of_mut!(l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28_once), _init_l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__28);
        v___x_2147_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__29;
        v___x_2148_ =
            l_Lean_addMacroScope(v_quotContext_2060_, v___x_2147_, v_currMacroScope_2061_);
        v___x_2149_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__31;
        v___x_2150_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2150_, 0, v___x_2067_);
        lean_ctor_set(v___x_2150_, 1, v___x_2146_);
        lean_ctor_set(v___x_2150_, 2, v___x_2148_);
        lean_ctor_set(v___x_2150_, 3, v___x_2149_);
        v___x_2151_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2102_, v___x_2103_, v___x_2150_);
        v___x_2152_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2151_);
        v___x_2153_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2152_);
        v___x_2154_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2153_);
        v___x_2155_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2098_, v___x_2100_, v___x_2154_);
        v___x_2156_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2072_, v___x_2145_, v___x_2155_);
        v___x_2157_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2096_, v___x_2097_, v___x_2156_);
        v___x_2158_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2157_);
        v___x_2159_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2158_);
        v___x_2160_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2159_);
        v___x_2161_ = l_Lean_Syntax_node3(
            v___x_2067_,
            v___x_2068_,
            v___x_2070_,
            v___x_2160_,
            v___x_2130_,
        );
        v___x_2162_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2161_);
        v___x_2163_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2162_);
        v___x_2164_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2163_);
        v___x_2165_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2092_, v___x_2094_, v___x_2164_);
        v___x_2166_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__10;
        v___x_2167_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_2168_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2168_, 0, v___x_2067_);
        lean_ctor_set(v___x_2168_, 1, v___x_2166_);
        v___x_2169_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2167_, v___x_2168_);
        v___x_2170_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2169_);
        v___x_2171_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2170_);
        v___x_2172_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2171_);
        v___x_2173_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2098_, v___x_2100_, v___x_2172_);
        v___x_2174_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2098_, v___x_2100_, v___x_2064_);
        v___x_2175_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__32;
        v___x_2176_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__33;
        v___x_2177_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2177_, 0, v___x_2067_);
        lean_ctor_set(v___x_2177_, 1, v___x_2175_);
        v___x_2178_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__35;
        v___x_2179_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__36;
        v___x_2180_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2180_, 0, v___x_2067_);
        lean_ctor_set(v___x_2180_, 1, v___x_2179_);
        v___x_2181_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2178_, v___x_2180_);
        v___x_2182_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2181_);
        v___x_2183_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2176_, v___x_2177_, v___x_2182_);
        v___x_2184_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2072_, v___x_2183_);
        v___x_2185_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2184_);
        v___x_2186_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2185_);
        v___x_2187_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2098_, v___x_2100_, v___x_2186_);
        v___x_2188_ = l_Lean_Syntax_node3(
            v___x_2067_,
            v___x_2072_,
            v___x_2173_,
            v___x_2174_,
            v___x_2187_,
        );
        v___x_2189_ = l_Lean_Syntax_node2(v___x_2067_, v___x_2096_, v___x_2097_, v___x_2188_);
        v___x_2190_ = lean_unsigned_to_nat(9);
        v___x_2191_ = lean_mk_empty_array_with_capacity(v___x_2190_);
        v___x_2192_ = lean_array_push(v___x_2191_, v___x_2076_);
        v___x_2193_ = lean_array_push(v___x_2192_, v___x_2078_);
        v___x_2194_ = lean_array_push(v___x_2193_, v___x_2091_);
        v___x_2195_ = lean_array_push(v___x_2194_, v___x_2078_);
        v___x_2196_ = lean_array_push(v___x_2195_, v___x_2135_);
        v___x_2197_ = lean_array_push(v___x_2196_, v___x_2078_);
        v___x_2198_ = lean_array_push(v___x_2197_, v___x_2165_);
        v___x_2199_ = lean_array_push(v___x_2198_, v___x_2078_);
        v___x_2200_ = lean_array_push(v___x_2199_, v___x_2189_);
        v___x_2201_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2201_, 0, v___x_2067_);
        lean_ctor_set(v___x_2201_, 1, v___x_2072_);
        lean_ctor_set(v___x_2201_, 2, v___x_2200_);
        v___x_2202_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2071_, v___x_2201_);
        v___x_2203_ = l_Lean_Syntax_node1(v___x_2067_, v___x_2065_, v___x_2202_);
        v___x_2204_ = l_Lean_Syntax_node3(
            v___x_2067_,
            v___x_2068_,
            v___x_2070_,
            v___x_2203_,
            v___x_2130_,
        );
        v___x_2205_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2205_, 0, v___x_2204_);
        lean_ctor_set(v___x_2205_, 1, v_a_2055_);
        return v___x_2205_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___boxed(
    mut v_x_2206_: *mut LeanObject,
    mut v_a_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2209_: *mut LeanObject = core::ptr::null_mut();
    v_res_2209_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1(
        v_x_2206_, v_a_2207_, v_a_2208_,
    );
    lean_dec_ref(v_a_2207_);
    return v_res_2209_;
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(
    mut v_x_2230_: *mut LeanObject,
    mut v_a_2231_: *mut LeanObject,
    mut v_a_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    v___x_2233_ = l_tacticDecreasing__tactic___closed__1;
    v___x_2234_ = l_Lean_Syntax_isOfKind(v_x_2230_, v___x_2233_);
    if v___x_2234_ == 0 {
        let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
        v___x_2235_ = lean_box(1);
        v___x_2236_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2236_, 0, v___x_2235_);
        lean_ctor_set(v___x_2236_, 1, v_a_2232_);
        return v___x_2236_;
    } else {
        let mut v_ref_2237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2238_: u8 = 0;
        let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
        v_ref_2237_ = lean_ctor_get(v_a_2231_, 5);
        v___x_2238_ = 0;
        v___x_2239_ = l_Lean_SourceInfo_fromRef(v_ref_2237_, v___x_2238_);
        v___x_2240_ = l_tacticDecreasing__with___00__closed__1;
        v___x_2241_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__0;
        lean_inc_n(v___x_2239_, 21);
        v___x_2242_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2242_, 0, v___x_2239_);
        lean_ctor_set(v___x_2242_, 1, v___x_2241_);
        v___x_2243_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__7;
        v___x_2244_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__9;
        v___x_2245_ = l___aux__Init__WFTactics______macroRules__tacticSimp__wf__1___closed__11;
        v___x_2246_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__3;
        v___x_2247_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__4;
        v___x_2248_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2248_, 0, v___x_2239_);
        lean_ctor_set(v___x_2248_, 1, v___x_2246_);
        v___x_2249_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__6;
        v___x_2250_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__with____1___closed__7;
        v___x_2251_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2251_, 0, v___x_2239_);
        lean_ctor_set(v___x_2251_, 1, v___x_2250_);
        v___x_2252_ = l_tacticDecreasing__trivial___closed__1;
        v___x_2253_ = l_tacticDecreasing__trivial___closed__2;
        v___x_2254_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2254_, 0, v___x_2239_);
        lean_ctor_set(v___x_2254_, 1, v___x_2253_);
        v___x_2255_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2252_, v___x_2254_);
        lean_inc(v___x_2255_);
        v___x_2256_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2245_, v___x_2255_);
        v___x_2257_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2244_, v___x_2256_);
        v___x_2258_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2243_, v___x_2257_);
        lean_inc_ref(v___x_2251_);
        v___x_2259_ = l_Lean_Syntax_node2(v___x_2239_, v___x_2249_, v___x_2251_, v___x_2258_);
        v___x_2260_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__2;
        v___x_2261_ =
            l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___closed__3;
        v___x_2262_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2262_, 0, v___x_2239_);
        lean_ctor_set(v___x_2262_, 1, v___x_2261_);
        v___x_2263_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2260_, v___x_2262_);
        v___x_2264_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__trivial__pre__omega__1___closed__10;
        v___x_2265_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2265_, 0, v___x_2239_);
        lean_ctor_set(v___x_2265_, 1, v___x_2264_);
        v___x_2266_ = l_Lean_Syntax_node3(
            v___x_2239_,
            v___x_2245_,
            v___x_2263_,
            v___x_2265_,
            v___x_2255_,
        );
        v___x_2267_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2244_, v___x_2266_);
        v___x_2268_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2243_, v___x_2267_);
        v___x_2269_ = l_Lean_Syntax_node2(v___x_2239_, v___x_2249_, v___x_2251_, v___x_2268_);
        v___x_2270_ = l_Lean_Syntax_node2(v___x_2239_, v___x_2245_, v___x_2259_, v___x_2269_);
        v___x_2271_ = l_Lean_Syntax_node2(v___x_2239_, v___x_2247_, v___x_2248_, v___x_2270_);
        v___x_2272_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2245_, v___x_2271_);
        v___x_2273_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2244_, v___x_2272_);
        v___x_2274_ = l_Lean_Syntax_node1(v___x_2239_, v___x_2243_, v___x_2273_);
        v___x_2275_ = l_Lean_Syntax_node2(v___x_2239_, v___x_2240_, v___x_2242_, v___x_2274_);
        v___x_2276_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2276_, 0, v___x_2275_);
        lean_ctor_set(v___x_2276_, 1, v_a_2232_);
        return v___x_2276_;
    }
}
pub unsafe fn l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1___boxed(
    mut v_x_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2280_: *mut LeanObject = core::ptr::null_mut();
    v_res_2280_ = l___aux__Init__WFTactics______macroRules__tacticDecreasing__tactic__1(
        v_x_2277_, v_a_2278_, v_a_2279_,
    );
    lean_dec_ref(v_a_2278_);
    return v_res_2280_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_WFTactics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_WFTactics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_WFTactics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_WFTactics(builtin);
}
