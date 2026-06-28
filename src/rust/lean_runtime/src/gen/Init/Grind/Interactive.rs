// Lean compiler output
// Module: Init.Grind.Interactive
// Imports: Init.Grind.Attr
use crate::r#gen::Init::Grind::Attr::{
    initialize_Init_Grind_Attr, l_Lean_Parser_Attr_grindMod, runtime_initialize_Init_Grind_Attr,
};
use crate::r#gen::Init::Notation::l_Lean_binderIdent;
use crate::r#gen::Init::Prelude::{
    l_Array_appendCore___redArg, l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
};
use crate::r#gen::Init::Tactics::l_Lean_Parser_Tactic_configItem;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_unsigned_to_nat,
};
pub static l_Lean_Parser_Tactic_anchor___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [97, 110, 99, 104, 111, 114, 0],
};
static mut l_Lean_Parser_Tactic_anchor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__1_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Parser_Tactic_anchor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Parser_Tactic_anchor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__3_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Parser_Tactic_anchor___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_anchor___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_anchor___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_anchor___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_anchor___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__0_value) as *mut LeanObject,
        12570470872972041128 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_anchor___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__5_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lean_Parser_Tactic_anchor___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__5_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_anchor___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__7_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [35, 0],
};
static mut l_Lean_Parser_Tactic_anchor___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__7_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_anchor___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__9_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 111, 87, 115, 0],
};
static mut l_Lean_Parser_Tactic_anchor___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__9_value) as *mut LeanObject,
        1581446985683836252 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_anchor___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__11_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_anchor___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_anchor___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__13_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [104, 101, 120, 110, 117, 109, 0],
};
static mut l_Lean_Parser_Tactic_anchor___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__13_value) as *mut LeanObject,
        11510626477845773464 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_anchor___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__15_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_anchor___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_anchor___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_anchor___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_anchor___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__17_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_anchor: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [103, 114, 105, 110, 100, 76, 101, 109, 109, 97, 0],
    };
static mut l_Lean_Parser_Tactic_grindLemma___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grindLemma___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__0_value) as *mut LeanObject,
        9605956393242244281 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__2_value: LeanStringObject<8> =
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
        m_data: [112, 112, 71, 114, 111, 117, 112, 0],
    };
static mut l_Lean_Parser_Tactic_grindLemma___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__2_value) as *mut LeanObject,
        15964447885077099669 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__4_value: LeanStringObject<9> =
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
        m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
    };
static mut l_Lean_Parser_Tactic_grindLemma___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__4_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__6_value: LeanStringObject<8> =
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
        m_data: [112, 112, 83, 112, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_grindLemma___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__6_value) as *mut LeanObject,
        17761616517784022991 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grindLemma___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindLemma___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grindLemma___closed__11_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_grindLemma___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__11_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemma___closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__12_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__13_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grindLemma___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindLemma___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindLemma___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindLemma___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grindLemma: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grindLemmaMin___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
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
            103, 114, 105, 110, 100, 76, 101, 109, 109, 97, 77, 105, 110, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__0_value)
                as *mut LeanObject,
            15805583526285245505 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemmaMin___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [33, 0],
    };
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindLemmaMin___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindLemmaMin___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grindLemmaMin: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grindErase___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [103, 114, 105, 110, 100, 69, 114, 97, 115, 101, 0],
    };
static mut l_Lean_Parser_Tactic_grindErase___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grindErase___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__0_value) as *mut LeanObject,
        8726292792893090987 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindErase___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindErase___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Parser_Tactic_grindErase___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindErase___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindErase___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindErase___closed__4_value: LeanStringObject<6> =
    LeanStringObject {
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
static mut l_Lean_Parser_Tactic_grindErase___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindErase___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__4_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindErase___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindErase___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindErase___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindErase___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindErase___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindErase___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindErase___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_grindErase: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindParam___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [103, 114, 105, 110, 100, 80, 97, 114, 97, 109, 0],
    };
static mut l_Lean_Parser_Tactic_grindParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grindParam___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__0_value) as *mut LeanObject,
        6042821575048204304 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindParam___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_grindParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindParam___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__2_value) as *mut LeanObject,
        393173242845875278 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grindParam___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindParam___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindParam___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindParam___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindParam___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindParam___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindParam___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindParam___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grindParam: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__0_value: LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value: LeanStringObject<5> =
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
        m_data: [113, 117, 111, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__0_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value)
                as *mut LeanObject,
            5855146430765573009 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3_value)
                as *mut LeanObject,
            14897043925059904963 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value)
                as *mut LeanObject,
            2128291854026903145 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__5_value: LeanStringObject<17> =
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
            96, 40, 103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 124, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__5_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__3_value)
                as *mut LeanObject,
            14897043925059904963 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__14_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filter_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__14_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Category_grind__filter: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__1_value: LeanStringObject<14> =
    LeanStringObject {
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
            103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 95, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__1_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__1_value)
                as *mut LeanObject,
            17749774379613861674 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__2_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__3_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filter__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__0_value: LeanStringObject<
    18,
> = LeanStringObject {
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 60, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_3: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__0_value)
            as *mut LeanObject,
        14191831149334518614 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__2_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [103, 101, 110, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__2_value)
            as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__4_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 60, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__5_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__4_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__6_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__7_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__8_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__7_value)
            as *mut LeanObject,
        6110315075117401315 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__8_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__10_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__11_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__1_value)
            as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__10_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__11_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__0_value: LeanStringObject<
    18,
> = LeanStringObject {
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_3: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__0_value)
            as *mut LeanObject,
        10897721082736832046 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__2_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 61, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__3_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__3_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__5_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__6_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__1_value)
            as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3d___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__0_value:
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 33, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_1:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_2:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_3:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__0_value
        ) as *mut LeanObject,
        12297617841168749882 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__2_value:
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
    m_data: [32, 33, 61, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__3_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__1_value
        ) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x21_x3d___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 17,
    m_data: [
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 226, 137, 164, 95,
        0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_1:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_2:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_3:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__0_value)
            as *mut LeanObject,
        13823788008300330912 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 137, 164, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__3_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__3_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__5_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__6_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__1_value)
            as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2264___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__0_value:
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 60, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_1:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_2:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_3:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__0_value
        ) as *mut LeanObject,
        13433549983839248510 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__2_value:
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
    m_data: [32, 60, 61, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__3_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__1_value
        ) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c_x3d___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__0_value: LeanStringObject<
    18,
> = LeanStringObject {
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 62, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_3: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__0_value)
            as *mut LeanObject,
        4600612048943183243 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__2_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 62, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__3_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__3_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__5_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__6_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__1_value)
            as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 17,
    m_data: [
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 226, 137, 165, 95,
        0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_1:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_2:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_3:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__0_value)
            as *mut LeanObject,
        2486500500062112323 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 137, 165, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__3_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__3_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__5_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__6_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__1_value)
            as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_u2265___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__0_value:
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 62, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_1:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_2:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_3:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value:
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
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__0_value
        ) as *mut LeanObject,
        4587601961659498949 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__2_value:
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
    m_data: [32, 62, 61, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__3_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__1_value
        ) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filterGen_x3e_x3d___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__0_value: LeanStringObject<
    16,
> = LeanStringObject {
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 40, 95, 41, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_3: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__0_value
            ) as *mut LeanObject,
            1261507149438490230 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2_value
            ) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__4_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__1_value
            ) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__5_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__0_value:
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 95, 38, 38, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_1:
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
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_2:
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
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_3:
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
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value:
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
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__0_value
        ) as *mut LeanObject,
        2546887458887176769 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__2_value:
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
    m_data: [32, 38, 38, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value)
            as *mut LeanObject,
        (((36 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__6_value:
    LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__1_value
        ) as *mut LeanObject,
        (((35 as usize) << 1) | 1) as *mut LeanObject,
        (((35 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__0_value:
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 95, 124, 124, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_1:
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
            l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_2:
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
            l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_3:
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
            l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value:
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
            l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__0_value
        ) as *mut LeanObject,
        13925358296987369388 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__2_value:
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
    m_data: [32, 124, 124, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x26_x26___00__closed__4_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__5_value:
    LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__1_value
        ) as *mut LeanObject,
        (((35 as usize) << 1) | 1) as *mut LeanObject,
        (((35 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__4_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___x7c_x7c___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__0_value: LeanStringObject<
    15,
> = LeanStringObject {
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
        103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 33, 95, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__0_value)
                as *mut LeanObject,
            1993779534650405055 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemmaMin___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__7_value)
                as *mut LeanObject,
            (((40 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__filter_x21__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x21___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindFilter___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [103, 114, 105, 110, 100, 70, 105, 108, 116, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindFilter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__0_value)
                as *mut LeanObject,
            12189819440004302135 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindFilter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindFilter___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [99, 111, 108, 71, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindFilter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindFilter___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__2_value)
                as *mut LeanObject,
            17597206043415342265 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindFilter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindFilter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindFilter___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindFilter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindFilter___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindFilter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindFilter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grindFilter: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__0_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value)
                as *mut LeanObject,
            6115385055951041549 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__2_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [96, 40, 103, 114, 105, 110, 100, 124, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__0_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_quot___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_grind: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [103, 114, 105, 110, 100, 83, 116, 101, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__0_value)
                as *mut LeanObject,
            6321866296242073541 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [124, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__8_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindStep___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grindStep: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
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
            103, 114, 105, 110, 100, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0_value)
                as *mut LeanObject,
            13326625262248817187 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__2_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            115, 101, 112, 66, 121, 49, 73, 110, 100, 101, 110, 116, 83, 101, 109, 105, 99, 111,
            108, 111, 110, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__2_value)
                as *mut LeanObject,
            12439213008700076310 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grindSeq1Indented: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
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
            103, 114, 105, 110, 100, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0_value)
                as *mut LeanObject,
            14378257753127062234 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [123, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__4_value: LeanStringObject<16> =
    LeanStringObject {
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
            119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__4_value)
                as *mut LeanObject,
            1164644006045091397 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__6_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            115, 101, 112, 66, 121, 73, 110, 100, 101, 110, 116, 83, 101, 109, 105, 99, 111, 108,
            111, 110, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__6_value)
                as *mut LeanObject,
            8450841259565682059 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__8_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindStep___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__11_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [125, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__11_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grindSeqBracketed: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeq___closed__0_value: LeanStringObject<9> =
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
        m_data: [103, 114, 105, 110, 100, 83, 101, 113, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__0_value)
                as *mut LeanObject,
            12547805878916670878 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeq___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__14_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindSeq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grindSeq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_paren___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_paren___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_paren___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__0_value) as *mut LeanObject,
        6341562230758934095 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_paren___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_paren___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_paren___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_paren___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_paren___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_paren___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_paren___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_paren___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_paren___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_paren: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_paren___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_skip___closed__0_value: LeanStringObject<5> =
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
        m_data: [115, 107, 105, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_skip___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_skip___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__0_value) as *mut LeanObject,
        3888978822640132046 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_skip___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_skip___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_skip___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_skip___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_skip___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_skip: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_skip___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_lia___closed__0_value: LeanStringObject<4> =
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
        m_data: [108, 105, 97, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_lia___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_lia___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__0_value) as *mut LeanObject,
        981545342569025135 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_lia___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_lia___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_lia___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_lia___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_lia___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_lia: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_lia___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_ring___closed__0_value: LeanStringObject<5> =
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
        m_data: [114, 105, 110, 103, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_ring___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_ring___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__0_value) as *mut LeanObject,
        16893285825895468094 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_ring___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_ring___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_ring___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_ring___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_ring___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_ring: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ring___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_ac___closed__0_value: LeanStringObject<3> =
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
        m_data: [97, 99, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_ac___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_ac___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__0_value) as *mut LeanObject,
        832305436351948166 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_ac___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_ac___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_ac___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_ac___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_ac___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_ac: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_ac___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_linarith___closed__0_value: LeanStringObject<9> =
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
        m_data: [108, 105, 110, 97, 114, 105, 116, 104, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_linarith___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_linarith___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__0_value)
                as *mut LeanObject,
            16351062939023608559 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_linarith___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_linarith___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_linarith___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_linarith___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_linarith___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_linarith: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_linarith___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_sorry___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [115, 111, 114, 114, 121, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_sorry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_sorry___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__0_value) as *mut LeanObject,
        12610174047474239361 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_sorry___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_sorry___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_sorry___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_sorry___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_sorry___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_sorry: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_sorry___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_thmNs___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 104, 109, 78, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_thmNs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__0_value) as *mut LeanObject,
        11601469613389255168 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_thmNs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_thmNs___closed__2_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 97, 109, 101, 115, 112, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_thmNs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_thmNs___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_thmNs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_thmNs___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_thmNs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_thmNs___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_thmNs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_thmNs: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thmNs___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_thm___closed__0_value: LeanStringObject<4> =
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
        m_data: [116, 104, 109, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_thm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thm___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_thm___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thm___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thm___closed__0_value) as *mut LeanObject,
        4493657671338864619 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_thm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_thm___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_thm___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_thm___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_thm___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_thm___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_thm___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_thm___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_thm___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_thm___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_thm: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__0_value)
                as *mut LeanObject,
            12928201877799427862 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__3_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [32, 111, 110, 108, 121, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__4_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__3_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__7_value: LeanStringObject<8> =
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
        m_data: [32, 97, 112, 112, 114, 111, 120, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__8_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__7_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__11_value: LeanStringObject<3> =
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
        m_data: [32, 91, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__13_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__14_value: LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__15_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__19_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_instantiate___closed__20_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__20_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_instantiate___closed__24: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_instantiate: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_use___closed__0_value: LeanStringObject<4> =
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
        m_data: [117, 115, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_use___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_use___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__0_value) as *mut LeanObject,
        4803991667162169508 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_use___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_use___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_use___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_use___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_use___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_use___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_use___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_use___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_use___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_use___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_use___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_use___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_use: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__0_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 110, 108, 121, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showAsserted___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [115, 104, 111, 119, 65, 115, 115, 101, 114, 116, 101, 100, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showAsserted___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__0_value)
                as *mut LeanObject,
            9307343899468237075 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showAsserted___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showAsserted___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
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
            115, 104, 111, 119, 95, 97, 115, 115, 101, 114, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showAsserted___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showAsserted___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showAsserted___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showAsserted___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showAsserted___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showAsserted___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showAsserted___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showAsserted___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showAsserted___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_showAsserted: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showAsserted___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTrue___closed__0_value: LeanStringObject<9> =
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
        m_data: [115, 104, 111, 119, 84, 114, 117, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showTrue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__0_value)
                as *mut LeanObject,
            13150684902857301386 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showTrue___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTrue___closed__2_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 104, 111, 119, 95, 116, 114, 117, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showTrue___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTrue___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showTrue___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTrue___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showTrue___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTrue___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showTrue___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTrue___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showTrue___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_showTrue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTrue___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showFalse___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 104, 111, 119, 70, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showFalse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__0_value)
                as *mut LeanObject,
            1698790517460571917 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showFalse___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showFalse___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [115, 104, 111, 119, 95, 102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showFalse___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showFalse___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showFalse___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showFalse___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showFalse___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showFalse___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showFalse___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showFalse___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showFalse___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_showFalse: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showFalse___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showEqcs___closed__0_value: LeanStringObject<9> =
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
        m_data: [115, 104, 111, 119, 69, 113, 99, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showEqcs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__0_value)
                as *mut LeanObject,
            15569771006456468598 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showEqcs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showEqcs___closed__2_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 104, 111, 119, 95, 101, 113, 99, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showEqcs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showEqcs___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showEqcs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showEqcs___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showEqcs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showEqcs___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showEqcs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showEqcs___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showEqcs___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_showEqcs: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showEqcs___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showCases___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 104, 111, 119, 67, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showCases___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_showCases___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__0_value)
                as *mut LeanObject,
            9341503222632710516 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showCases___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showCases___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [115, 104, 111, 119, 95, 99, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showCases___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showCases___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showCases___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showCases___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showCases___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showCases___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showCases___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showCases___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showCases___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_showCases: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showCases___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showState___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 104, 111, 119, 83, 116, 97, 116, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_showState___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__0_value)
                as *mut LeanObject,
            10137114440480477384 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showState___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showState___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [115, 104, 111, 119, 95, 115, 116, 97, 116, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showState___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showState___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showState___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showState___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showState___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showState___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showState___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showState___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showState___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_showState: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showState___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showLocalThms___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
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
            115, 104, 111, 119, 76, 111, 99, 97, 108, 84, 104, 109, 115, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showLocalThms___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__0_value)
                as *mut LeanObject,
            17299153005056664641 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showLocalThms___closed__2_value: LeanStringObject<16> =
    LeanStringObject {
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
            115, 104, 111, 119, 95, 108, 111, 99, 97, 108, 95, 116, 104, 109, 115, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showLocalThms___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showLocalThms___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showLocalThms___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showLocalThms___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showLocalThms___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_showLocalThms: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showLocalThms___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTerm___closed__0_value: LeanStringObject<9> =
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
        m_data: [115, 104, 111, 119, 84, 101, 114, 109, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showTerm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__0_value)
                as *mut LeanObject,
            11271821878211811031 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showTerm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTerm___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [115, 104, 111, 119, 95, 116, 101, 114, 109, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showTerm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTerm___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showTerm___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTerm___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showTerm___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showTerm___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showTerm___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_showTerm: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showTerm___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showGoals___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 104, 111, 119, 71, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showGoals___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__0_value)
                as *mut LeanObject,
            4913389825418561202 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showGoals___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showGoals___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [115, 104, 111, 119, 95, 103, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_showGoals___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showGoals___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showGoals___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_showGoals___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_showGoals___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_showGoals: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_showGoals___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [103, 114, 105, 110, 100, 95, 114, 101, 102, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0_value)
                as *mut LeanObject,
            6513229495683628353 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__1_value)
                as *mut LeanObject,
            7058010524799864595 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
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
            96, 40, 103, 114, 105, 110, 100, 95, 114, 101, 102, 124, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__0_value)
                as *mut LeanObject,
            6513229495683628353 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__2_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__ref_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Category_grind__ref: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [103, 114, 105, 110, 100, 95, 114, 101, 102, 95, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__0_value)
                as *mut LeanObject,
            11143388761733130988 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__17_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__ref__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [103, 114, 105, 110, 100, 95, 114, 101, 102, 95, 95, 49, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__0_value)
                as *mut LeanObject,
            9463332226020071253 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind__ref____1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref____1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_cases___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [99, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_cases___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_cases___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__0_value) as *mut LeanObject,
        9932274655851112959 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_cases___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_cases___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [99, 97, 115, 101, 115, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_cases___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_cases___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_cases___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_cases___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__ref_quot___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_cases___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_cases___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_cases___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_cases: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_cases___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_casesTrace___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [99, 97, 115, 101, 115, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_casesTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__0_value)
                as *mut LeanObject,
            17771192587646415388 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_casesTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_casesTrace___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [99, 97, 115, 101, 115, 63, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_casesTrace___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_casesTrace___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_casesTrace___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_casesTrace___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_casesTrace___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_casesTrace___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_casesTrace___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_casesTrace: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesTrace___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_casesNext___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [99, 97, 115, 101, 115, 78, 101, 120, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_casesNext___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__0_value)
                as *mut LeanObject,
            1094407643885780061 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_casesNext___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_casesNext___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [99, 97, 115, 101, 115, 95, 110, 101, 120, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_casesNext___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_casesNext___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_casesNext___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_casesNext___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_casesNext___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_casesNext: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_casesNext___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_done___closed__0_value: LeanStringObject<5> =
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
        m_data: [100, 111, 110, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_done___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_done___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__0_value) as *mut LeanObject,
        4707943553582391371 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_done___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_done___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_done___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_done___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_done___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_done: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_done___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_finish___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [102, 105, 110, 105, 115, 104, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_finish___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_finish___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__0_value)
                as *mut LeanObject,
            15503256039972703489 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_finish___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_finish___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_finish___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_finish___closed__3_value: LeanStringObject<5> =
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
        m_data: [109, 97, 110, 121, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_finish___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_finish___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__3_value)
                as *mut LeanObject,
            2302572775315350313 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_finish___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__4_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_finish___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finish___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finish___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_finish___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 6 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2_value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Grind_finish___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_finish___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_finish___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_finish___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_finish___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finish___closed__10_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_finish___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finish___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finish___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finish___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finish___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finish___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finish___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finish___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finish___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_finish: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_finishTrace___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [102, 105, 110, 105, 115, 104, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__0_value)
                as *mut LeanObject,
            10423707108080707712 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_finishTrace___closed__2_value: LeanStringObject<8> =
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
        m_data: [102, 105, 110, 105, 115, 104, 63, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_finishTrace___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_finishTrace___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_finishTrace: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_have___closed__0_value: LeanStringObject<5> =
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
        m_data: [104, 97, 118, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_have___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_have___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__0_value) as *mut LeanObject,
        13243635457614750868 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_have___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_have___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_have___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_have___closed__3_value: LeanStringObject<8> =
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
        m_data: [108, 101, 116, 68, 101, 99, 108, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_have___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_have___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__3_value) as *mut LeanObject,
        15062419370142113517 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_have___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_have___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_have___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_have___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_have___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_have___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_have___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_have: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__0_value: LeanStringObject<17> =
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
            110, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 67, 111, 114, 101, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__0_value)
                as *mut LeanObject,
            11599023979573974026 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__4_value: LeanStringObject<5> =
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
        m_data: [32, 61, 62, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7_value: LeanStringObject<10> =
    LeanStringObject {
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
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7_value)
                as *mut LeanObject,
            11103865283154438669 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__11_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_nestedTacticCore: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_allGoals___closed__0_value: LeanStringObject<9> =
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
        m_data: [97, 108, 108, 71, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_allGoals___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__0_value)
                as *mut LeanObject,
            2460877087228735619 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_allGoals___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_allGoals___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_allGoals___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_allGoals___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_allGoals___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_allGoals___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_allGoals___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_allGoals___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_allGoals___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_allGoals: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_allGoals___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_focus___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 111, 99, 117, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_focus___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_focus___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__0_value) as *mut LeanObject,
        10062717289844655180 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_focus___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_focus___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [102, 111, 99, 117, 115, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_focus___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_focus___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_focus___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_focus___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_focus___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_focus___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_focus___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_focus: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_focus___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_next___closed__0_value: LeanStringObject<5> =
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
        m_data: [110, 101, 120, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_next___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_next___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__0_value) as *mut LeanObject,
        7819112639170036602 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_next___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_next___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [110, 101, 120, 116, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_next___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_next___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_next___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_next___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_next___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_next___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_next___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_next___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_next___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_next___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_next___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_next___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_next___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_next___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_next: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 7,
        m_data: [103, 114, 105, 110, 100, 194, 183, 95, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__0_value)
                as *mut LeanObject,
            12389819025714499611 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 2,
        m_data: [194, 183, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__3_value: LeanStringObject<3> =
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
        m_data: [46, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 12,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__3_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind_xb7__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_anyGoals___closed__0_value: LeanStringObject<9> =
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
        m_data: [97, 110, 121, 71, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_anyGoals___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__0_value)
                as *mut LeanObject,
            3049087452712666050 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_anyGoals___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_anyGoals___closed__2_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [97, 110, 121, 95, 103, 111, 97, 108, 115, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_anyGoals___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_anyGoals___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_anyGoals___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_anyGoals___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_anyGoals___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_anyGoals___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_anyGoals___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_anyGoals: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_anyGoals___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
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
            119, 105, 116, 104, 65, 110, 110, 111, 116, 97, 116, 101, 83, 116, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__0_value)
                as *mut LeanObject,
            13439077436853187233 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__2_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            119, 105, 116, 104, 95, 97, 110, 110, 111, 116, 97, 116, 101, 95, 115, 116, 97, 116,
            101, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__4_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [114, 97, 119, 83, 116, 120, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__4_value)
                as *mut LeanObject,
            7922007774678457419 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__5_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__10_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_withAnnotateState: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__0_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [103, 114, 105, 110, 100, 95, 60, 59, 62, 95, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_3: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
            as *mut LeanObject,
        3168557723425139092 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__0_value
            ) as *mut LeanObject,
            17356226235442988904 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__2_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 60, 59, 62, 32, 0],
};
static mut l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__4_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind_quot___closed__4_value)
                as *mut LeanObject,
            (((2 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__3_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__4_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__6_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1_value
            ) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__5_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [119, 105, 116, 104, 95, 97, 110, 110, 111, 116, 97, 116, 101, 95, 115, 116, 97, 116, 101, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 105, 114, 115, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_first___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__0_value) as *mut LeanObject,
        1872589449178528769 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_first___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [102, 105, 114, 115, 116, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_first___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__4_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Grind_first___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__4_value) as *mut LeanObject,
        17180264478054591478 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_first___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__6_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Grind_first___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__6_value) as *mut LeanObject,
        17243740965612849207 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_first___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__8_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Grind_first___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__8_value) as *mut LeanObject,
        2214559063752339918 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_first___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__10_value: LeanStringObject<9> =
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
        m_data: [112, 112, 68, 101, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__10_value)
                as *mut LeanObject,
            2710995909225096690 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__12_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Grind_first___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__12_value)
                as *mut LeanObject,
            4227538229121138037 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__14_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__15_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__16_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Grind_first___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__16_value)
                as *mut LeanObject,
            4942254933594350711 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__18_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__18_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__19_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__19_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__20_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__21_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__19_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__21_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__22_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__21_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__22_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__23_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__22_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__23_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__24_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__24_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__25_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__24_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__25_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__26_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__25_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__26_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__27_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__26_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__27_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_first___closed__28_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__27_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_first___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__28_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_first: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__28_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [103, 114, 105, 110, 100, 84, 114, 121, 95, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindTry___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__0_value)
                as *mut LeanObject,
            12836141112798546983 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__2_value: LeanStringObject<5> =
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
        m_data: [116, 114, 121, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindTry___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindTry___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindTry___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindTry___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindTry___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grindTry__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindTry___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
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
            102, 97, 105, 108, 73, 102, 83, 117, 99, 99, 101, 115, 115, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__0_value)
                as *mut LeanObject,
            3513798075453532937 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__2_value: LeanStringObject<17> =
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
            102, 97, 105, 108, 95, 105, 102, 95, 115, 117, 99, 99, 101, 115, 115, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_failIfSuccess: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_failIfSuccess___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindAdmit___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [103, 114, 105, 110, 100, 65, 100, 109, 105, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindAdmit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__0_value)
                as *mut LeanObject,
            5710066338182857729 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindAdmit___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [97, 100, 109, 105, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindAdmit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindAdmit___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindAdmit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindAdmit___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindAdmit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grindAdmit: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindAdmit___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_fail___closed__0_value: LeanStringObject<5> =
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
        m_data: [102, 97, 105, 108, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_fail___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_fail___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__0_value) as *mut LeanObject,
        13025226898844494529 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_fail___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_fail___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_fail___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_fail___closed__3_value: LeanStringObject<4> =
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
        m_data: [115, 116, 114, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_fail___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_fail___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__3_value) as *mut LeanObject,
        9232979286016572671 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_fail___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_fail___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_fail___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_fail___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_fail___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_fail___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_fail___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_fail___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_fail___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_fail___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_fail___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_fail: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_fail___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [103, 114, 105, 110, 100, 82, 101, 112, 101, 97, 116, 95, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__0_value)
                as *mut LeanObject,
            6640407548456426915 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__2_value: LeanStringObject<8> =
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
        m_data: [114, 101, 112, 101, 97, 116, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grindRepeat__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 112, 101, 97, 116, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_renameI___closed__0_value: LeanStringObject<8> =
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
        m_data: [114, 101, 110, 97, 109, 101, 73, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_renameI___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__0_value)
                as *mut LeanObject,
            15282284598227900718 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_renameI___closed__2_value: LeanStringObject<9> =
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
        m_data: [114, 101, 110, 97, 109, 101, 95, 105, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_renameI___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_renameI___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindFilter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__4_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_renameI___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_renameI: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_exposeNames___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [101, 120, 112, 111, 115, 101, 78, 97, 109, 101, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_exposeNames___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__0_value)
                as *mut LeanObject,
            11368832657924028223 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_exposeNames___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_exposeNames___closed__2_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [101, 120, 112, 111, 115, 101, 95, 110, 97, 109, 101, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_exposeNames___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_exposeNames___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_exposeNames___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_exposeNames___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_exposeNames___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_exposeNames: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_exposeNames___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 101, 116, 79, 112, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__0_value)
                as *mut LeanObject,
            7389052539099382846 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [46, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__11_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__11_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__13_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [111, 112, 116, 105, 111, 110, 86, 97, 108, 117, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__13_value)
                as *mut LeanObject,
            9900369431690160525 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__17_value: LeanStringObject<5> =
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
        m_data: [32, 105, 110, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__18_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__18_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__19_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__19_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__20_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__19_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindSeq___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setOption___closed__21_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setOption___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__21_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_setOption: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setOption___closed__21_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setConfig___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 101, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__0_value)
                as *mut LeanObject,
            4143932667249891471 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setConfig___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [115, 101, 116, 95, 99, 111, 110, 102, 105, 103, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_setConfig___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_setConfig___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_setConfig___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_setConfig: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [104, 97, 118, 101, 83, 105, 108, 101, 110, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__0_value)
                as *mut LeanObject,
            4733526434027481274 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_have___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__6_value: LeanStringObject<3> =
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
        m_data: [58, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_haveSilent___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_haveSilent___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__10_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_haveSilent: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_haveSilent___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_mbtc___closed__0_value: LeanStringObject<5> =
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
        m_data: [109, 98, 116, 99, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_mbtc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__0_value) as *mut LeanObject,
        17215256822346630302 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_mbtc___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_mbtc___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_mbtc___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_mbtc___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Grind_mbtc___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_mbtc: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_mbtc___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__0_value: LeanStringObject<9> =
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
        m_data: [115, 121, 109, 73, 110, 116, 114, 111, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__0_value)
                as *mut LeanObject,
            18071745766926037277 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [105, 110, 116, 114, 111, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_first___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__5_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__5_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__8_value: LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value: LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 111, 107, 101, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value)
                as *mut LeanObject,
            9392652980833654105 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value)
                as *mut LeanObject,
            2332914473072559713 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__14_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value)
                as *mut LeanObject,
            9392652980833654105 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value)
                as *mut LeanObject,
            12399226076480050666 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__18_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__18_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__19_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__17_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__19_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__20_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__21_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__21_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__22_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__21_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__22_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__23_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__23_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntro___closed__24_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__24_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_symIntro___closed__27: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_symIntro: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
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
            115, 121, 109, 73, 110, 116, 114, 111, 76, 105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__0_value)
                as *mut LeanObject,
            6317774695141850336 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__11_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__3_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [126, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Grind_symIntroLight: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntros___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 121, 109, 73, 110, 116, 114, 111, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntros___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__0_value)
                as *mut LeanObject,
            2346161484485275443 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntros___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntros___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 110, 116, 114, 111, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntros___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntros___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntros___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntros___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntros___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntros___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntros___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_symIntros: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
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
            115, 121, 109, 73, 110, 116, 114, 111, 115, 76, 105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__0_value)
                as *mut LeanObject,
            6153970908091088054 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntros___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__11_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_symIntrosLight: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symApply___closed__0_value: LeanStringObject<9> =
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
        m_data: [115, 121, 109, 65, 112, 112, 108, 121, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symApply___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symApply___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__0_value)
                as *mut LeanObject,
            5374856426837570639 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symApply___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symApply___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [97, 112, 112, 108, 121, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symApply___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symApply___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symApply___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symApply___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symApply___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symApply___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symApply___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_symApply: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symApply___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symInternalize___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
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
            115, 121, 109, 73, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__0_value)
                as *mut LeanObject,
            1043145629818708985 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalize___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symInternalize___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_grind__filterGen_x3c___00__closed__9_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalize___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symInternalize___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalize___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symInternalize___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalize___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symInternalize___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalize___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_symInternalize: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalize___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
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
            115, 121, 109, 73, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 65, 108, 108, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__0_value)
                as *mut LeanObject,
            3904094997328998658 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__2_value: LeanStringObject<16> =
    LeanStringObject {
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
            105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 95, 97, 108, 108, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_symInternalizeAll: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symInternalizeAll___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symByContra___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [115, 121, 109, 66, 121, 67, 111, 110, 116, 114, 97, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symByContra___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__0_value)
                as *mut LeanObject,
            13968308769098880762 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symByContra___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symByContra___closed__2_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [98, 121, 95, 99, 111, 110, 116, 114, 97, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symByContra___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symByContra___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symByContra___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symByContra___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symByContra___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_symByContra: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symByContra___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__0_value: LeanStringObject<8> =
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
        m_data: [115, 121, 109, 83, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__0_value)
                as *mut LeanObject,
            18174426835286715810 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__2_value: LeanStringObject<5> =
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
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_renameI___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__7_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 10,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__15_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symSimp___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symSimp___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__12_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_symSimp: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__0_value: LeanStringObject<9> =
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
        m_data: [115, 121, 109, 68, 83, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__0_value)
                as *mut LeanObject,
            3963057966736669232 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [100, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symSimp___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [42, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symIntro___closed__12_value)
                as *mut LeanObject,
            9392652980833654105 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value)
                as *mut LeanObject,
            5671119348926085934 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindParam___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindErase___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__10_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 10,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__15_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_instantiate___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__13_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_symDSimp___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_symDSimp___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__15_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_symDSimp: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_symDSimp___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [103, 114, 105, 110, 100, 69, 120, 97, 99, 116, 95, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindExact___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grind__filter___00__closed__0_value)
                as *mut LeanObject,
            3168557723425139092 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__0_value)
                as *mut LeanObject,
            11082219180989694881 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [101, 120, 97, 99, 116, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Grind_grindExact___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindExact___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindLemma___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindExact___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind_grindExact___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Grind_grindExact___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Grind_grindExact__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_grindExact___00__closed__5_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__7_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__1_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__1_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__1_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_anchor___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3_value) as *mut LeanObject,14997215300048349804 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemma___closed__9() -> *mut LeanObject {
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    v___x_2698_ = l_Lean_Parser_Tactic_grindLemma___closed__8;
    v___x_2699_ = l_Lean_Parser_Attr_grindMod;
    v___x_2700_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_2701_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2701_, 0, v___x_2700_);
    lean_ctor_set(v___x_2701_, 1, v___x_2699_);
    lean_ctor_set(v___x_2701_, 2, v___x_2698_);
    return v___x_2701_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemma___closed__10() -> *mut LeanObject {
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    v___x_2702_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__9_once),
        _init_l_Lean_Parser_Tactic_grindLemma___closed__9,
    );
    v___x_2703_ = l_Lean_Parser_Tactic_grindLemma___closed__5;
    v___x_2704_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2704_, 0, v___x_2703_);
    lean_ctor_set(v___x_2704_, 1, v___x_2702_);
    return v___x_2704_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemma___closed__14() -> *mut LeanObject {
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    v___x_2711_ = l_Lean_Parser_Tactic_grindLemma___closed__13;
    v___x_2712_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__10_once),
        _init_l_Lean_Parser_Tactic_grindLemma___closed__10,
    );
    v___x_2713_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_2714_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2714_, 0, v___x_2713_);
    lean_ctor_set(v___x_2714_, 1, v___x_2712_);
    lean_ctor_set(v___x_2714_, 2, v___x_2711_);
    return v___x_2714_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemma___closed__15() -> *mut LeanObject {
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    v___x_2715_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__14_once),
        _init_l_Lean_Parser_Tactic_grindLemma___closed__14,
    );
    v___x_2716_ = l_Lean_Parser_Tactic_grindLemma___closed__3;
    v___x_2717_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2717_, 0, v___x_2716_);
    lean_ctor_set(v___x_2717_, 1, v___x_2715_);
    return v___x_2717_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemma___closed__16() -> *mut LeanObject {
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    v___x_2718_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__15_once),
        _init_l_Lean_Parser_Tactic_grindLemma___closed__15,
    );
    v___x_2719_ = l_Lean_Parser_Tactic_grindLemma___closed__1;
    v___x_2720_ = l_Lean_Parser_Tactic_grindLemma___closed__0;
    v___x_2721_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_2721_, 0, v___x_2720_);
    lean_ctor_set(v___x_2721_, 1, v___x_2719_);
    lean_ctor_set(v___x_2721_, 2, v___x_2718_);
    return v___x_2721_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemma() -> *mut LeanObject {
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    v___x_2722_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__16_once),
        _init_l_Lean_Parser_Tactic_grindLemma___closed__16,
    );
    return v___x_2722_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__4() -> *mut LeanObject {
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    v___x_2732_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemma___closed__10_once),
        _init_l_Lean_Parser_Tactic_grindLemma___closed__10,
    );
    v___x_2733_ = l_Lean_Parser_Tactic_grindLemmaMin___closed__3;
    v___x_2734_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_2735_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2735_, 0, v___x_2734_);
    lean_ctor_set(v___x_2735_, 1, v___x_2733_);
    lean_ctor_set(v___x_2735_, 2, v___x_2732_);
    return v___x_2735_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__5() -> *mut LeanObject {
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    v___x_2736_ = l_Lean_Parser_Tactic_grindLemma___closed__13;
    v___x_2737_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemmaMin___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemmaMin___closed__4_once),
        _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__4,
    );
    v___x_2738_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_2739_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2739_, 0, v___x_2738_);
    lean_ctor_set(v___x_2739_, 1, v___x_2737_);
    lean_ctor_set(v___x_2739_, 2, v___x_2736_);
    return v___x_2739_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__6() -> *mut LeanObject {
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    v___x_2740_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemmaMin___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemmaMin___closed__5_once),
        _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__5,
    );
    v___x_2741_ = l_Lean_Parser_Tactic_grindLemma___closed__3;
    v___x_2742_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2742_, 0, v___x_2741_);
    lean_ctor_set(v___x_2742_, 1, v___x_2740_);
    return v___x_2742_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__7() -> *mut LeanObject {
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    v___x_2743_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemmaMin___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemmaMin___closed__6_once),
        _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__6,
    );
    v___x_2744_ = l_Lean_Parser_Tactic_grindLemmaMin___closed__1;
    v___x_2745_ = l_Lean_Parser_Tactic_grindLemmaMin___closed__0;
    v___x_2746_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_2746_, 0, v___x_2745_);
    lean_ctor_set(v___x_2746_, 1, v___x_2744_);
    lean_ctor_set(v___x_2746_, 2, v___x_2743_);
    return v___x_2746_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindLemmaMin() -> *mut LeanObject {
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    v___x_2747_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemmaMin___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindLemmaMin___closed__7_once),
        _init_l_Lean_Parser_Tactic_grindLemmaMin___closed__7,
    );
    return v___x_2747_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindParam___closed__4() -> *mut LeanObject {
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    v___x_2780_ = l_Lean_Parser_Tactic_anchor;
    v___x_2781_ = l_Lean_Parser_Tactic_grindLemma;
    v___x_2782_ = l_Lean_Parser_Tactic_grindParam___closed__3;
    v___x_2783_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2783_, 0, v___x_2782_);
    lean_ctor_set(v___x_2783_, 1, v___x_2781_);
    lean_ctor_set(v___x_2783_, 2, v___x_2780_);
    return v___x_2783_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindParam___closed__5() -> *mut LeanObject {
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    v___x_2784_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindParam___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindParam___closed__4_once),
        _init_l_Lean_Parser_Tactic_grindParam___closed__4,
    );
    v___x_2785_ = l_Lean_Parser_Tactic_grindLemmaMin;
    v___x_2786_ = l_Lean_Parser_Tactic_grindParam___closed__3;
    v___x_2787_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2787_, 0, v___x_2786_);
    lean_ctor_set(v___x_2787_, 1, v___x_2785_);
    lean_ctor_set(v___x_2787_, 2, v___x_2784_);
    return v___x_2787_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindParam___closed__6() -> *mut LeanObject {
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    v___x_2788_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindParam___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindParam___closed__5_once),
        _init_l_Lean_Parser_Tactic_grindParam___closed__5,
    );
    v___x_2789_ = l_Lean_Parser_Tactic_grindErase;
    v___x_2790_ = l_Lean_Parser_Tactic_grindParam___closed__3;
    v___x_2791_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_2791_, 0, v___x_2790_);
    lean_ctor_set(v___x_2791_, 1, v___x_2789_);
    lean_ctor_set(v___x_2791_, 2, v___x_2788_);
    return v___x_2791_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindParam___closed__7() -> *mut LeanObject {
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    v___x_2792_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindParam___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindParam___closed__6_once),
        _init_l_Lean_Parser_Tactic_grindParam___closed__6,
    );
    v___x_2793_ = l_Lean_Parser_Tactic_grindParam___closed__1;
    v___x_2794_ = l_Lean_Parser_Tactic_grindParam___closed__0;
    v___x_2795_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_2795_, 0, v___x_2794_);
    lean_ctor_set(v___x_2795_, 1, v___x_2793_);
    lean_ctor_set(v___x_2795_, 2, v___x_2792_);
    return v___x_2795_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindParam() -> *mut LeanObject {
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    v___x_2796_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindParam___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindParam___closed__7_once),
        _init_l_Lean_Parser_Tactic_grindParam___closed__7,
    );
    return v___x_2796_;
}
pub unsafe fn _init_l_Lean_Parser_Category_grind__filter() -> *mut LeanObject {
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    v___x_2836_ = lean_box(0);
    return v___x_2836_;
}
pub unsafe fn _init_l_Lean_Parser_Category_grind() -> *mut LeanObject {
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    v___x_3183_ = lean_box(0);
    return v___x_3183_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_thm___closed__2() -> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_Parser_Tactic_grindLemma;
    v___x_3434_ = l_Lean_Parser_Tactic_grindLemmaMin;
    v___x_3435_ = l_Lean_Parser_Tactic_grindParam___closed__3;
    v___x_3436_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3436_, 0, v___x_3435_);
    lean_ctor_set(v___x_3436_, 1, v___x_3434_);
    lean_ctor_set(v___x_3436_, 2, v___x_3433_);
    return v___x_3436_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_thm___closed__3() -> *mut LeanObject {
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3437_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_thm___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_thm___closed__2_once),
        _init_l_Lean_Parser_Tactic_Grind_thm___closed__2,
    );
    v___x_3438_ = l_Lean_Parser_Tactic_Grind_thmNs;
    v___x_3439_ = l_Lean_Parser_Tactic_grindParam___closed__3;
    v___x_3440_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3440_, 0, v___x_3439_);
    lean_ctor_set(v___x_3440_, 1, v___x_3438_);
    lean_ctor_set(v___x_3440_, 2, v___x_3437_);
    return v___x_3440_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_thm___closed__4() -> *mut LeanObject {
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    v___x_3441_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_thm___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_thm___closed__3_once),
        _init_l_Lean_Parser_Tactic_Grind_thm___closed__3,
    );
    v___x_3442_ = l_Lean_Parser_Tactic_anchor;
    v___x_3443_ = l_Lean_Parser_Tactic_grindParam___closed__3;
    v___x_3444_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3444_, 0, v___x_3443_);
    lean_ctor_set(v___x_3444_, 1, v___x_3442_);
    lean_ctor_set(v___x_3444_, 2, v___x_3441_);
    return v___x_3444_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_thm___closed__5() -> *mut LeanObject {
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    v___x_3445_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_thm___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_thm___closed__4_once),
        _init_l_Lean_Parser_Tactic_Grind_thm___closed__4,
    );
    v___x_3446_ = l_Lean_Parser_Tactic_Grind_thm___closed__1;
    v___x_3447_ = l_Lean_Parser_Tactic_Grind_thm___closed__0;
    v___x_3448_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_3448_, 0, v___x_3447_);
    lean_ctor_set(v___x_3448_, 1, v___x_3446_);
    lean_ctor_set(v___x_3448_, 2, v___x_3445_);
    return v___x_3448_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_thm() -> *mut LeanObject {
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    v___x_3449_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_thm___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_thm___closed__5_once),
        _init_l_Lean_Parser_Tactic_Grind_thm___closed__5,
    );
    return v___x_3449_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__16() -> *mut LeanObject {
    let mut v___x_3489_: u8 = 0;
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    v___x_3489_ = 1;
    v___x_3490_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__15;
    v___x_3491_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__13;
    v___x_3492_ = l_Lean_Parser_Tactic_Grind_thm;
    v___x_3493_ = lean_alloc_ctor(10, 3, (1) as u32);
    lean_ctor_set(v___x_3493_, 0, v___x_3492_);
    lean_ctor_set(v___x_3493_, 1, v___x_3491_);
    lean_ctor_set(v___x_3493_, 2, v___x_3490_);
    lean_ctor_set_uint8(
        v___x_3493_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_3489_,
    );
    return v___x_3493_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__17() -> *mut LeanObject {
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    v___x_3494_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__16_once),
        _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__16,
    );
    v___x_3495_ = l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5;
    v___x_3496_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3496_, 0, v___x_3495_);
    lean_ctor_set(v___x_3496_, 1, v___x_3494_);
    return v___x_3496_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__18() -> *mut LeanObject {
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    v___x_3497_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__17_once),
        _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__17,
    );
    v___x_3498_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__12;
    v___x_3499_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3500_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3500_, 0, v___x_3499_);
    lean_ctor_set(v___x_3500_, 1, v___x_3498_);
    lean_ctor_set(v___x_3500_, 2, v___x_3497_);
    return v___x_3500_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__21() -> *mut LeanObject {
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    v___x_3504_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__20;
    v___x_3505_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__18_once),
        _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__18,
    );
    v___x_3506_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3507_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3507_, 0, v___x_3506_);
    lean_ctor_set(v___x_3507_, 1, v___x_3505_);
    lean_ctor_set(v___x_3507_, 2, v___x_3504_);
    return v___x_3507_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__22() -> *mut LeanObject {
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    v___x_3508_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__21_once),
        _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__21,
    );
    v___x_3509_ = l_Lean_Parser_Tactic_grindLemma___closed__5;
    v___x_3510_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3510_, 0, v___x_3509_);
    lean_ctor_set(v___x_3510_, 1, v___x_3508_);
    return v___x_3510_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__23() -> *mut LeanObject {
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    v___x_3511_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__22_once),
        _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__22,
    );
    v___x_3512_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__10;
    v___x_3513_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3514_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3514_, 0, v___x_3513_);
    lean_ctor_set(v___x_3514_, 1, v___x_3512_);
    lean_ctor_set(v___x_3514_, 2, v___x_3511_);
    return v___x_3514_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__24() -> *mut LeanObject {
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    v___x_3515_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__23_once),
        _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__23,
    );
    v___x_3516_ = lean_unsigned_to_nat(1022);
    v___x_3517_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__1;
    v___x_3518_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_3518_, 0, v___x_3517_);
    lean_ctor_set(v___x_3518_, 1, v___x_3516_);
    lean_ctor_set(v___x_3518_, 2, v___x_3515_);
    return v___x_3518_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_instantiate() -> *mut LeanObject {
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    v___x_3519_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__24_once),
        _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__24,
    );
    return v___x_3519_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_use___closed__4() -> *mut LeanObject {
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    v___x_3534_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_instantiate___closed__17_once),
        _init_l_Lean_Parser_Tactic_Grind_instantiate___closed__17,
    );
    v___x_3535_ = l_Lean_Parser_Tactic_Grind_use___closed__3;
    v___x_3536_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3537_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3537_, 0, v___x_3536_);
    lean_ctor_set(v___x_3537_, 1, v___x_3535_);
    lean_ctor_set(v___x_3537_, 2, v___x_3534_);
    return v___x_3537_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_use___closed__5() -> *mut LeanObject {
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    v___x_3538_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__20;
    v___x_3539_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_use___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_use___closed__4_once),
        _init_l_Lean_Parser_Tactic_Grind_use___closed__4,
    );
    v___x_3540_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3541_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3541_, 0, v___x_3540_);
    lean_ctor_set(v___x_3541_, 1, v___x_3539_);
    lean_ctor_set(v___x_3541_, 2, v___x_3538_);
    return v___x_3541_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_use___closed__6() -> *mut LeanObject {
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    v___x_3542_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_use___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_use___closed__5_once),
        _init_l_Lean_Parser_Tactic_Grind_use___closed__5,
    );
    v___x_3543_ = lean_unsigned_to_nat(1024);
    v___x_3544_ = l_Lean_Parser_Tactic_Grind_use___closed__1;
    v___x_3545_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_3545_, 0, v___x_3544_);
    lean_ctor_set(v___x_3545_, 1, v___x_3543_);
    lean_ctor_set(v___x_3545_, 2, v___x_3542_);
    return v___x_3545_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_use() -> *mut LeanObject {
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    v___x_3546_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_use___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_use___closed__6_once),
        _init_l_Lean_Parser_Tactic_Grind_use___closed__6,
    );
    return v___x_3546_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3()
-> *mut LeanObject {
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    v___x_3551_ = l_Array_mkArray0(lean_box(0));
    return v___x_3551_;
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1(
    mut v_x_3553_: *mut LeanObject,
    mut v_a_3554_: *mut LeanObject,
    mut v_a_3555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: u8 = 0;
    v___x_3556_ = l_Lean_Parser_Tactic_Grind_use___closed__1;
    lean_inc(v_x_3553_);
    v___x_3557_ = l_Lean_Syntax_isOfKind(v_x_3553_, v___x_3556_);
    if v___x_3557_ == 0 {
        let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3553_);
        v___x_3558_ = lean_box(1);
        v___x_3559_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3559_, 0, v___x_3558_);
        lean_ctor_set(v___x_3559_, 1, v_a_3555_);
        return v___x_3559_;
    } else {
        let mut v_ref_3560_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_3562_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3566_: u8 = 0;
        let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
        v_ref_3560_ = lean_ctor_get(v_a_3554_, 5);
        v___x_3561_ = lean_unsigned_to_nat(0);
        v_u_3562_ = l_Lean_Syntax_getArg(v_x_3553_, v___x_3561_);
        v___x_3563_ = lean_unsigned_to_nat(2);
        v___x_3564_ = l_Lean_Syntax_getArg(v_x_3553_, v___x_3563_);
        lean_dec(v_x_3553_);
        v___x_3565_ = l_Lean_Syntax_getArgs(v___x_3564_);
        lean_dec(v___x_3564_);
        v___x_3566_ = 0;
        v___x_3567_ = l_Lean_SourceInfo_fromRef(v_ref_3560_, v___x_3566_);
        v___x_3568_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__0;
        v___x_3569_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__1;
        v___x_3570_ = l_Lean_SourceInfo_fromRef(v_u_3562_, v___x_3557_);
        lean_dec(v_u_3562_);
        v___x_3571_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3571_, 0, v___x_3570_);
        lean_ctor_set(v___x_3571_, 1, v___x_3568_);
        v___x_3572_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1;
        v___x_3573_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__2;
        lean_inc_n(v___x_3567_, 7);
        v___x_3574_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3574_, 0, v___x_3567_);
        lean_ctor_set(v___x_3574_, 1, v___x_3573_);
        v___x_3575_ = l_Lean_Syntax_node1(v___x_3567_, v___x_3572_, v___x_3574_);
        v___x_3576_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once), _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
        v___x_3577_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_3577_, 0, v___x_3567_);
        lean_ctor_set(v___x_3577_, 1, v___x_3572_);
        lean_ctor_set(v___x_3577_, 2, v___x_3576_);
        v___x_3578_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__4;
        v___x_3579_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3579_, 0, v___x_3567_);
        lean_ctor_set(v___x_3579_, 1, v___x_3578_);
        v___x_3580_ = l_Array_appendCore___redArg(v___x_3576_, v___x_3565_);
        lean_dec_ref(v___x_3565_);
        v___x_3581_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_3581_, 0, v___x_3567_);
        lean_ctor_set(v___x_3581_, 1, v___x_3572_);
        lean_ctor_set(v___x_3581_, 2, v___x_3580_);
        v___x_3582_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__19;
        v___x_3583_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3583_, 0, v___x_3567_);
        lean_ctor_set(v___x_3583_, 1, v___x_3582_);
        v___x_3584_ = l_Lean_Syntax_node3(
            v___x_3567_,
            v___x_3572_,
            v___x_3579_,
            v___x_3581_,
            v___x_3583_,
        );
        v___x_3585_ = l_Lean_Syntax_node4(
            v___x_3567_,
            v___x_3569_,
            v___x_3571_,
            v___x_3575_,
            v___x_3577_,
            v___x_3584_,
        );
        v___x_3586_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3586_, 0, v___x_3585_);
        lean_ctor_set(v___x_3586_, 1, v_a_3555_);
        return v___x_3586_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___boxed(
    mut v_x_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
    mut v_a_3589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3590_: *mut LeanObject = core::ptr::null_mut();
    v_res_3590_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1(v_x_3587_, v_a_3588_, v_a_3589_);
    lean_dec_ref(v_a_3588_);
    return v_res_3590_;
}
pub unsafe fn _init_l_Lean_Parser_Category_grind__ref() -> *mut LeanObject {
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    v___x_3816_ = lean_box(0);
    return v___x_3816_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__5() -> *mut LeanObject {
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    v___x_3925_ = l_Lean_Parser_Tactic_configItem;
    v___x_3926_ = l_Lean_Parser_Tactic_grindLemma___closed__8;
    v___x_3927_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3928_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3928_, 0, v___x_3927_);
    lean_ctor_set(v___x_3928_, 1, v___x_3926_);
    lean_ctor_set(v___x_3928_, 2, v___x_3925_);
    return v___x_3928_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__6() -> *mut LeanObject {
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    v___x_3929_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__5_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__5,
    );
    v___x_3930_ = l_Lean_Parser_Tactic_Grind_finish___closed__4;
    v___x_3931_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3931_, 0, v___x_3930_);
    lean_ctor_set(v___x_3931_, 1, v___x_3929_);
    return v___x_3931_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__7() -> *mut LeanObject {
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    v___x_3932_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__6_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__6,
    );
    v___x_3933_ = l_Lean_Parser_Tactic_Grind_finish___closed__2;
    v___x_3934_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3935_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3935_, 0, v___x_3934_);
    lean_ctor_set(v___x_3935_, 1, v___x_3933_);
    lean_ctor_set(v___x_3935_, 2, v___x_3932_);
    return v___x_3935_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__11() -> *mut LeanObject {
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    v___x_3946_ = l_Lean_Parser_Tactic_Grind_finish___closed__10;
    v___x_3947_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__7_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__7,
    );
    v___x_3948_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3949_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3949_, 0, v___x_3948_);
    lean_ctor_set(v___x_3949_, 1, v___x_3947_);
    lean_ctor_set(v___x_3949_, 2, v___x_3946_);
    return v___x_3949_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__12() -> *mut LeanObject {
    let mut v___x_3950_: u8 = 0;
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    v___x_3950_ = 0;
    v___x_3951_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__15;
    v___x_3952_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__13;
    v___x_3953_ = l_Lean_Parser_Tactic_grindParam;
    v___x_3954_ = lean_alloc_ctor(10, 3, (1) as u32);
    lean_ctor_set(v___x_3954_, 0, v___x_3953_);
    lean_ctor_set(v___x_3954_, 1, v___x_3952_);
    lean_ctor_set(v___x_3954_, 2, v___x_3951_);
    lean_ctor_set_uint8(
        v___x_3954_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_3950_,
    );
    return v___x_3954_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__13() -> *mut LeanObject {
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    v___x_3955_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__12_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__12,
    );
    v___x_3956_ = l_Lean_Parser_Tactic_Grind_grindSeqBracketed___closed__5;
    v___x_3957_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3957_, 0, v___x_3956_);
    lean_ctor_set(v___x_3957_, 1, v___x_3955_);
    return v___x_3957_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__14() -> *mut LeanObject {
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    v___x_3958_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__13_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__13,
    );
    v___x_3959_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__12;
    v___x_3960_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3961_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3961_, 0, v___x_3960_);
    lean_ctor_set(v___x_3961_, 1, v___x_3959_);
    lean_ctor_set(v___x_3961_, 2, v___x_3958_);
    return v___x_3961_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__15() -> *mut LeanObject {
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    v___x_3962_ = l_Lean_Parser_Tactic_Grind_instantiate___closed__20;
    v___x_3963_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__14_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__14,
    );
    v___x_3964_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3965_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3965_, 0, v___x_3964_);
    lean_ctor_set(v___x_3965_, 1, v___x_3963_);
    lean_ctor_set(v___x_3965_, 2, v___x_3962_);
    return v___x_3965_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__16() -> *mut LeanObject {
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    v___x_3966_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__15_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__15,
    );
    v___x_3967_ = l_Lean_Parser_Tactic_grindLemma___closed__5;
    v___x_3968_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3968_, 0, v___x_3967_);
    lean_ctor_set(v___x_3968_, 1, v___x_3966_);
    return v___x_3968_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__17() -> *mut LeanObject {
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    v___x_3969_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__16_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__16,
    );
    v___x_3970_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__11_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__11,
    );
    v___x_3971_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3972_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3972_, 0, v___x_3971_);
    lean_ctor_set(v___x_3972_, 1, v___x_3970_);
    lean_ctor_set(v___x_3972_, 2, v___x_3969_);
    return v___x_3972_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish___closed__18() -> *mut LeanObject {
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    v___x_3973_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__17_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__17,
    );
    v___x_3974_ = lean_unsigned_to_nat(1022);
    v___x_3975_ = l_Lean_Parser_Tactic_Grind_finish___closed__1;
    v___x_3976_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_3976_, 0, v___x_3975_);
    lean_ctor_set(v___x_3976_, 1, v___x_3974_);
    lean_ctor_set(v___x_3976_, 2, v___x_3973_);
    return v___x_3976_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finish() -> *mut LeanObject {
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    v___x_3977_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__18_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__18,
    );
    return v___x_3977_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__4() -> *mut LeanObject {
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    v___x_3989_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__6_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__6,
    );
    v___x_3990_ = l_Lean_Parser_Tactic_Grind_finishTrace___closed__3;
    v___x_3991_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3992_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3992_, 0, v___x_3991_);
    lean_ctor_set(v___x_3992_, 1, v___x_3990_);
    lean_ctor_set(v___x_3992_, 2, v___x_3989_);
    return v___x_3992_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__5() -> *mut LeanObject {
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    v___x_3993_ = l_Lean_Parser_Tactic_Grind_finish___closed__10;
    v___x_3994_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__4_once),
        _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__4,
    );
    v___x_3995_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_3996_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3996_, 0, v___x_3995_);
    lean_ctor_set(v___x_3996_, 1, v___x_3994_);
    lean_ctor_set(v___x_3996_, 2, v___x_3993_);
    return v___x_3996_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__6() -> *mut LeanObject {
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    v___x_3997_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finish___closed__16_once),
        _init_l_Lean_Parser_Tactic_Grind_finish___closed__16,
    );
    v___x_3998_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__5_once),
        _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__5,
    );
    v___x_3999_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4000_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4000_, 0, v___x_3999_);
    lean_ctor_set(v___x_4000_, 1, v___x_3998_);
    lean_ctor_set(v___x_4000_, 2, v___x_3997_);
    return v___x_4000_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__7() -> *mut LeanObject {
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    v___x_4001_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__6_once),
        _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__6,
    );
    v___x_4002_ = lean_unsigned_to_nat(1022);
    v___x_4003_ = l_Lean_Parser_Tactic_Grind_finishTrace___closed__1;
    v___x_4004_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4004_, 0, v___x_4003_);
    lean_ctor_set(v___x_4004_, 1, v___x_4002_);
    lean_ctor_set(v___x_4004_, 2, v___x_4001_);
    return v___x_4004_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_finishTrace() -> *mut LeanObject {
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    v___x_4005_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_finishTrace___closed__7_once),
        _init_l_Lean_Parser_Tactic_Grind_finishTrace___closed__7,
    );
    return v___x_4005_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_next___closed__4() -> *mut LeanObject {
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    v___x_4113_ = l_Lean_binderIdent;
    v___x_4114_ = l_Lean_Parser_Tactic_Grind_finish___closed__4;
    v___x_4115_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4115_, 0, v___x_4114_);
    lean_ctor_set(v___x_4115_, 1, v___x_4113_);
    return v___x_4115_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_next___closed__5() -> *mut LeanObject {
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    v___x_4116_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__4_once),
        _init_l_Lean_Parser_Tactic_Grind_next___closed__4,
    );
    v___x_4117_ = l_Lean_Parser_Tactic_Grind_next___closed__3;
    v___x_4118_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4119_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4119_, 0, v___x_4118_);
    lean_ctor_set(v___x_4119_, 1, v___x_4117_);
    lean_ctor_set(v___x_4119_, 2, v___x_4116_);
    return v___x_4119_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_next___closed__6() -> *mut LeanObject {
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    v___x_4120_ = l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__5;
    v___x_4121_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__5_once),
        _init_l_Lean_Parser_Tactic_Grind_next___closed__5,
    );
    v___x_4122_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4123_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4123_, 0, v___x_4122_);
    lean_ctor_set(v___x_4123_, 1, v___x_4121_);
    lean_ctor_set(v___x_4123_, 2, v___x_4120_);
    return v___x_4123_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_next___closed__7() -> *mut LeanObject {
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    v___x_4124_ = l_Lean_Parser_Tactic_Grind_grindSeq;
    v___x_4125_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__6_once),
        _init_l_Lean_Parser_Tactic_Grind_next___closed__6,
    );
    v___x_4126_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4127_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4127_, 0, v___x_4126_);
    lean_ctor_set(v___x_4127_, 1, v___x_4125_);
    lean_ctor_set(v___x_4127_, 2, v___x_4124_);
    return v___x_4127_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_next___closed__8() -> *mut LeanObject {
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    v___x_4128_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__7_once),
        _init_l_Lean_Parser_Tactic_Grind_next___closed__7,
    );
    v___x_4129_ = lean_unsigned_to_nat(1022);
    v___x_4130_ = l_Lean_Parser_Tactic_Grind_next___closed__1;
    v___x_4131_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4131_, 0, v___x_4130_);
    lean_ctor_set(v___x_4131_, 1, v___x_4129_);
    lean_ctor_set(v___x_4131_, 2, v___x_4128_);
    return v___x_4131_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_next() -> *mut LeanObject {
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    v___x_4132_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_next___closed__8_once),
        _init_l_Lean_Parser_Tactic_Grind_next___closed__8,
    );
    return v___x_4132_;
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1(
    mut v_x_4156_: *mut LeanObject,
    mut v_a_4157_: *mut LeanObject,
    mut v_a_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: u8 = 0;
    v___x_4159_ = l_Lean_Parser_Tactic_Grind_grind_xb7___00__closed__1;
    lean_inc(v_x_4156_);
    v___x_4160_ = l_Lean_Syntax_isOfKind(v_x_4156_, v___x_4159_);
    if v___x_4160_ == 0 {
        let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4156_);
        v___x_4161_ = lean_box(1);
        v___x_4162_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4162_, 0, v___x_4161_);
        lean_ctor_set(v___x_4162_, 1, v_a_4158_);
        return v___x_4162_;
    } else {
        let mut v_ref_4163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4168_: u8 = 0;
        let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4163_ = lean_ctor_get(v_a_4157_, 5);
        v___x_4164_ = lean_unsigned_to_nat(0);
        v___x_4165_ = l_Lean_Syntax_getArg(v_x_4156_, v___x_4164_);
        v___x_4166_ = lean_unsigned_to_nat(1);
        v___x_4167_ = l_Lean_Syntax_getArg(v_x_4156_, v___x_4166_);
        lean_dec(v_x_4156_);
        v___x_4168_ = 0;
        v___x_4169_ = l_Lean_SourceInfo_fromRef(v_ref_4163_, v___x_4168_);
        v___x_4170_ = l_Lean_Parser_Tactic_Grind_next___closed__0;
        v___x_4171_ = l_Lean_Parser_Tactic_Grind_next___closed__1;
        v___x_4172_ = l_Lean_SourceInfo_fromRef(v___x_4165_, v___x_4160_);
        lean_dec(v___x_4165_);
        lean_inc(v___x_4172_);
        v___x_4173_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4173_, 0, v___x_4172_);
        lean_ctor_set(v___x_4173_, 1, v___x_4170_);
        v___x_4174_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1;
        v___x_4175_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once), _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
        lean_inc(v___x_4169_);
        v___x_4176_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_4176_, 0, v___x_4169_);
        lean_ctor_set(v___x_4176_, 1, v___x_4174_);
        lean_ctor_set(v___x_4176_, 2, v___x_4175_);
        v___x_4177_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0;
        v___x_4178_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4178_, 0, v___x_4172_);
        lean_ctor_set(v___x_4178_, 1, v___x_4177_);
        v___x_4179_ = l_Lean_Syntax_node4(
            v___x_4169_,
            v___x_4171_,
            v___x_4173_,
            v___x_4176_,
            v___x_4178_,
            v___x_4167_,
        );
        v___x_4180_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4180_, 0, v___x_4179_);
        lean_ctor_set(v___x_4180_, 1, v_a_4158_);
        return v___x_4180_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___boxed(
    mut v_x_4181_: *mut LeanObject,
    mut v_a_4182_: *mut LeanObject,
    mut v_a_4183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4184_: *mut LeanObject = core::ptr::null_mut();
    v_res_4184_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1(v_x_4181_, v_a_4182_, v_a_4183_);
    lean_dec_ref(v_a_4182_);
    return v_res_4184_;
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1(
    mut v_x_4264_: *mut LeanObject,
    mut v_a_4265_: *mut LeanObject,
    mut v_a_4266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    v___x_4267_ = l_Lean_Parser_Tactic_Grind_grind___x3c_x3b_x3e___00__closed__1;
    lean_inc(v_x_4264_);
    v___x_4268_ = l_Lean_Syntax_isOfKind(v_x_4264_, v___x_4267_);
    if v___x_4268_ == 0 {
        let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4264_);
        v___x_4269_ = lean_box(1);
        v___x_4270_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4270_, 0, v___x_4269_);
        lean_ctor_set(v___x_4270_, 1, v_a_4266_);
        return v___x_4270_;
    } else {
        let mut v_ref_4271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tk_4275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4278_: u8 = 0;
        let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4271_ = lean_ctor_get(v_a_4265_, 5);
        v___x_4272_ = lean_unsigned_to_nat(0);
        v___x_4273_ = l_Lean_Syntax_getArg(v_x_4264_, v___x_4272_);
        v___x_4274_ = lean_unsigned_to_nat(1);
        v_tk_4275_ = l_Lean_Syntax_getArg(v_x_4264_, v___x_4274_);
        v___x_4276_ = lean_unsigned_to_nat(2);
        v___x_4277_ = l_Lean_Syntax_getArg(v_x_4264_, v___x_4276_);
        lean_dec(v_x_4264_);
        v___x_4278_ = 0;
        v___x_4279_ = l_Lean_SourceInfo_fromRef(v_ref_4271_, v___x_4278_);
        v___x_4280_ = l_Lean_Parser_Tactic_Grind_focus___closed__0;
        v___x_4281_ = l_Lean_Parser_Tactic_Grind_focus___closed__1;
        lean_inc_n(v___x_4279_, 18);
        v___x_4282_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4282_, 0, v___x_4279_);
        lean_ctor_set(v___x_4282_, 1, v___x_4280_);
        v___x_4283_ = l_Lean_Parser_Tactic_Grind_grindSeq___closed__1;
        v___x_4284_ = l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1;
        v___x_4285_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1;
        v___x_4286_ = l_Lean_Parser_Tactic_Grind_grindStep___closed__1;
        v___x_4287_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once), _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
        v___x_4288_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_4288_, 0, v___x_4279_);
        lean_ctor_set(v___x_4288_, 1, v___x_4285_);
        lean_ctor_set(v___x_4288_, 2, v___x_4287_);
        lean_inc_ref_n(v___x_4288_, 5);
        v___x_4289_ = l_Lean_Syntax_node2(v___x_4279_, v___x_4286_, v___x_4273_, v___x_4288_);
        v___x_4290_ = l_Lean_Parser_Tactic_Grind_withAnnotateState___closed__1;
        v___x_4291_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__0;
        v___x_4292_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4292_, 0, v___x_4279_);
        lean_ctor_set(v___x_4292_, 1, v___x_4291_);
        v___x_4293_ = l_Lean_Parser_Tactic_Grind_skip___closed__0;
        v___x_4294_ = l_Lean_Parser_Tactic_Grind_skip___closed__1;
        v___x_4295_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4295_, 0, v___x_4279_);
        lean_ctor_set(v___x_4295_, 1, v___x_4293_);
        v___x_4296_ = l_Lean_Syntax_node1(v___x_4279_, v___x_4294_, v___x_4295_);
        v___x_4297_ = l_Lean_Syntax_node3(
            v___x_4279_,
            v___x_4290_,
            v___x_4292_,
            v_tk_4275_,
            v___x_4296_,
        );
        v___x_4298_ = l_Lean_Syntax_node2(v___x_4279_, v___x_4286_, v___x_4297_, v___x_4288_);
        v___x_4299_ = l_Lean_Parser_Tactic_Grind_allGoals___closed__1;
        v___x_4300_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___closed__1;
        v___x_4301_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4301_, 0, v___x_4279_);
        lean_ctor_set(v___x_4301_, 1, v___x_4300_);
        v___x_4302_ = l_Lean_Syntax_node2(v___x_4279_, v___x_4286_, v___x_4277_, v___x_4288_);
        v___x_4303_ = l_Lean_Syntax_node1(v___x_4279_, v___x_4285_, v___x_4302_);
        v___x_4304_ = l_Lean_Syntax_node1(v___x_4279_, v___x_4284_, v___x_4303_);
        v___x_4305_ = l_Lean_Syntax_node1(v___x_4279_, v___x_4283_, v___x_4304_);
        v___x_4306_ = l_Lean_Syntax_node2(v___x_4279_, v___x_4299_, v___x_4301_, v___x_4305_);
        v___x_4307_ = l_Lean_Syntax_node2(v___x_4279_, v___x_4286_, v___x_4306_, v___x_4288_);
        v___x_4308_ = l_Lean_Syntax_node5(
            v___x_4279_,
            v___x_4285_,
            v___x_4289_,
            v___x_4288_,
            v___x_4298_,
            v___x_4288_,
            v___x_4307_,
        );
        v___x_4309_ = l_Lean_Syntax_node1(v___x_4279_, v___x_4284_, v___x_4308_);
        v___x_4310_ = l_Lean_Syntax_node1(v___x_4279_, v___x_4283_, v___x_4309_);
        v___x_4311_ = l_Lean_Syntax_node2(v___x_4279_, v___x_4281_, v___x_4282_, v___x_4310_);
        v___x_4312_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4312_, 0, v___x_4311_);
        lean_ctor_set(v___x_4312_, 1, v_a_4266_);
        return v___x_4312_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1___boxed(
    mut v_x_4313_: *mut LeanObject,
    mut v_a_4314_: *mut LeanObject,
    mut v_a_4315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4316_: *mut LeanObject = core::ptr::null_mut();
    v_res_4316_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind___x3c_x3b_x3e____1(v_x_4313_, v_a_4314_, v_a_4315_);
    lean_dec_ref(v_a_4314_);
    return v_res_4316_;
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1(
    mut v_x_4409_: *mut LeanObject,
    mut v_a_4410_: *mut LeanObject,
    mut v_a_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: u8 = 0;
    v___x_4412_ = l_Lean_Parser_Tactic_Grind_grindTry___00__closed__1;
    lean_inc(v_x_4409_);
    v___x_4413_ = l_Lean_Syntax_isOfKind(v_x_4409_, v___x_4412_);
    if v___x_4413_ == 0 {
        let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4409_);
        v___x_4414_ = lean_box(1);
        v___x_4415_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4415_, 0, v___x_4414_);
        lean_ctor_set(v___x_4415_, 1, v_a_4411_);
        return v___x_4415_;
    } else {
        let mut v_ref_4416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4420_: u8 = 0;
        let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4416_ = lean_ctor_get(v_a_4410_, 5);
        v___x_4417_ = lean_unsigned_to_nat(1);
        v___x_4418_ = l_Lean_Syntax_getArg(v_x_4409_, v___x_4417_);
        lean_dec(v_x_4409_);
        v___x_4419_ = l_Lean_Parser_Tactic_Grind_grindSeq___closed__1;
        v___x_4420_ = 0;
        v___x_4421_ = l_Lean_SourceInfo_fromRef(v_ref_4416_, v___x_4420_);
        v___x_4422_ = l_Lean_Parser_Tactic_Grind_first___closed__0;
        v___x_4423_ = l_Lean_Parser_Tactic_Grind_first___closed__1;
        lean_inc_n(v___x_4421_, 13);
        v___x_4424_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4424_, 0, v___x_4421_);
        lean_ctor_set(v___x_4424_, 1, v___x_4422_);
        v___x_4425_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1;
        v___x_4426_ = l_Lean_Parser_Tactic_Grind_first___closed__9;
        v___x_4427_ = l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2;
        v___x_4428_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4428_, 0, v___x_4421_);
        lean_ctor_set(v___x_4428_, 1, v___x_4427_);
        v___x_4429_ = l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9;
        v___x_4430_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4430_, 0, v___x_4421_);
        lean_ctor_set(v___x_4430_, 1, v___x_4429_);
        lean_inc_ref(v___x_4430_);
        lean_inc_ref(v___x_4428_);
        v___x_4431_ = l_Lean_Syntax_node3(
            v___x_4421_,
            v___x_4426_,
            v___x_4428_,
            v___x_4418_,
            v___x_4430_,
        );
        v___x_4432_ = l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1;
        v___x_4433_ = l_Lean_Parser_Tactic_Grind_grindStep___closed__1;
        v___x_4434_ = l_Lean_Parser_Tactic_Grind_skip___closed__0;
        v___x_4435_ = l_Lean_Parser_Tactic_Grind_skip___closed__1;
        v___x_4436_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4436_, 0, v___x_4421_);
        lean_ctor_set(v___x_4436_, 1, v___x_4434_);
        v___x_4437_ = l_Lean_Syntax_node1(v___x_4421_, v___x_4435_, v___x_4436_);
        v___x_4438_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once), _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
        v___x_4439_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_4439_, 0, v___x_4421_);
        lean_ctor_set(v___x_4439_, 1, v___x_4425_);
        lean_ctor_set(v___x_4439_, 2, v___x_4438_);
        v___x_4440_ = l_Lean_Syntax_node2(v___x_4421_, v___x_4433_, v___x_4437_, v___x_4439_);
        v___x_4441_ = l_Lean_Syntax_node1(v___x_4421_, v___x_4425_, v___x_4440_);
        v___x_4442_ = l_Lean_Syntax_node1(v___x_4421_, v___x_4432_, v___x_4441_);
        v___x_4443_ = l_Lean_Syntax_node1(v___x_4421_, v___x_4419_, v___x_4442_);
        v___x_4444_ = l_Lean_Syntax_node3(
            v___x_4421_,
            v___x_4426_,
            v___x_4428_,
            v___x_4443_,
            v___x_4430_,
        );
        v___x_4445_ = l_Lean_Syntax_node2(v___x_4421_, v___x_4425_, v___x_4431_, v___x_4444_);
        v___x_4446_ = l_Lean_Syntax_node2(v___x_4421_, v___x_4423_, v___x_4424_, v___x_4445_);
        v___x_4447_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4447_, 0, v___x_4446_);
        lean_ctor_set(v___x_4447_, 1, v_a_4411_);
        return v___x_4447_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1___boxed(
    mut v_x_4448_: *mut LeanObject,
    mut v_a_4449_: *mut LeanObject,
    mut v_a_4450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4451_: *mut LeanObject = core::ptr::null_mut();
    v_res_4451_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindTry____1(v_x_4448_, v_a_4449_, v_a_4450_);
    lean_dec_ref(v_a_4449_);
    return v_res_4451_;
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1(
    mut v_x_4488_: *mut LeanObject,
    mut v_a_4489_: *mut LeanObject,
    mut v_a_4490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: u8 = 0;
    v___x_4491_ = l_Lean_Parser_Tactic_Grind_grindAdmit___closed__1;
    v___x_4492_ = l_Lean_Syntax_isOfKind(v_x_4488_, v___x_4491_);
    if v___x_4492_ == 0 {
        let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
        v___x_4493_ = lean_box(1);
        v___x_4494_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4494_, 0, v___x_4493_);
        lean_ctor_set(v___x_4494_, 1, v_a_4490_);
        return v___x_4494_;
    } else {
        let mut v_ref_4495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4496_: u8 = 0;
        let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4495_ = lean_ctor_get(v_a_4489_, 5);
        v___x_4496_ = 0;
        v___x_4497_ = l_Lean_SourceInfo_fromRef(v_ref_4495_, v___x_4496_);
        v___x_4498_ = l_Lean_Parser_Tactic_Grind_sorry___closed__0;
        v___x_4499_ = l_Lean_Parser_Tactic_Grind_sorry___closed__1;
        lean_inc(v___x_4497_);
        v___x_4500_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4500_, 0, v___x_4497_);
        lean_ctor_set(v___x_4500_, 1, v___x_4498_);
        v___x_4501_ = l_Lean_Syntax_node1(v___x_4497_, v___x_4499_, v___x_4500_);
        v___x_4502_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4502_, 0, v___x_4501_);
        lean_ctor_set(v___x_4502_, 1, v_a_4490_);
        return v___x_4502_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1___boxed(
    mut v_x_4503_: *mut LeanObject,
    mut v_a_4504_: *mut LeanObject,
    mut v_a_4505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4506_: *mut LeanObject = core::ptr::null_mut();
    v_res_4506_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindAdmit__1(v_x_4503_, v_a_4504_, v_a_4505_);
    lean_dec_ref(v_a_4504_);
    return v_res_4506_;
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1(
    mut v_x_4560_: *mut LeanObject,
    mut v_a_4561_: *mut LeanObject,
    mut v_a_4562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    v___x_4563_ = l_Lean_Parser_Tactic_Grind_grindRepeat___00__closed__1;
    lean_inc(v_x_4560_);
    v___x_4564_ = l_Lean_Syntax_isOfKind(v_x_4560_, v___x_4563_);
    if v___x_4564_ == 0 {
        let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4560_);
        v___x_4565_ = lean_box(1);
        v___x_4566_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4566_, 0, v___x_4565_);
        lean_ctor_set(v___x_4566_, 1, v_a_4562_);
        return v___x_4566_;
    } else {
        let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4570_: u8 = 0;
        v___x_4567_ = lean_unsigned_to_nat(1);
        v___x_4568_ = l_Lean_Syntax_getArg(v_x_4560_, v___x_4567_);
        lean_dec(v_x_4560_);
        v___x_4569_ = l_Lean_Parser_Tactic_Grind_grindSeq___closed__1;
        lean_inc(v___x_4568_);
        v___x_4570_ = l_Lean_Syntax_isOfKind(v___x_4568_, v___x_4569_);
        if v___x_4570_ == 0 {
            let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4568_);
            v___x_4571_ = lean_box(1);
            v___x_4572_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_4572_, 0, v___x_4571_);
            lean_ctor_set(v___x_4572_, 1, v_a_4562_);
            return v___x_4572_;
        } else {
            let mut v_ref_4573_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4574_: u8 = 0;
            let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
            v_ref_4573_ = lean_ctor_get(v_a_4561_, 5);
            v___x_4574_ = 0;
            v___x_4575_ = l_Lean_SourceInfo_fromRef(v_ref_4573_, v___x_4574_);
            v___x_4576_ = l_Lean_Parser_Tactic_Grind_first___closed__0;
            v___x_4577_ = l_Lean_Parser_Tactic_Grind_first___closed__1;
            lean_inc_n(v___x_4575_, 22);
            v___x_4578_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_4578_, 0, v___x_4575_);
            lean_ctor_set(v___x_4578_, 1, v___x_4576_);
            v___x_4579_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1;
            v___x_4580_ = l_Lean_Parser_Tactic_Grind_first___closed__9;
            v___x_4581_ = l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2;
            v___x_4582_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_4582_, 0, v___x_4575_);
            lean_ctor_set(v___x_4582_, 1, v___x_4581_);
            v___x_4583_ = l_Lean_Parser_Tactic_Grind_grindSeq1Indented___closed__1;
            v___x_4584_ = l_Lean_Parser_Tactic_Grind_grindStep___closed__1;
            v___x_4585_ = l_Lean_Parser_Tactic_Grind_paren___closed__1;
            v___x_4586_ = l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9;
            v___x_4587_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_4587_, 0, v___x_4575_);
            lean_ctor_set(v___x_4587_, 1, v___x_4586_);
            lean_inc_ref_n(v___x_4587_, 2);
            lean_inc(v___x_4568_);
            lean_inc_ref_n(v___x_4582_, 2);
            v___x_4588_ = l_Lean_Syntax_node3(
                v___x_4575_,
                v___x_4585_,
                v___x_4582_,
                v___x_4568_,
                v___x_4587_,
            );
            v___x_4589_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once), _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
            v___x_4590_ = lean_alloc_ctor(1, 3, (0) as u32);
            lean_ctor_set(v___x_4590_, 0, v___x_4575_);
            lean_ctor_set(v___x_4590_, 1, v___x_4579_);
            lean_ctor_set(v___x_4590_, 2, v___x_4589_);
            lean_inc_ref_n(v___x_4590_, 2);
            v___x_4591_ = l_Lean_Syntax_node2(v___x_4575_, v___x_4584_, v___x_4588_, v___x_4590_);
            v___x_4592_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__0;
            v___x_4593_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_4593_, 0, v___x_4575_);
            lean_ctor_set(v___x_4593_, 1, v___x_4592_);
            v___x_4594_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___closed__1;
            v___x_4595_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_4595_, 0, v___x_4575_);
            lean_ctor_set(v___x_4595_, 1, v___x_4594_);
            v___x_4596_ = l_Lean_Syntax_node2(v___x_4575_, v___x_4563_, v___x_4595_, v___x_4568_);
            v___x_4597_ = l_Lean_Syntax_node2(v___x_4575_, v___x_4584_, v___x_4596_, v___x_4590_);
            v___x_4598_ = l_Lean_Syntax_node3(
                v___x_4575_,
                v___x_4579_,
                v___x_4591_,
                v___x_4593_,
                v___x_4597_,
            );
            v___x_4599_ = l_Lean_Syntax_node1(v___x_4575_, v___x_4583_, v___x_4598_);
            v___x_4600_ = l_Lean_Syntax_node1(v___x_4575_, v___x_4569_, v___x_4599_);
            v___x_4601_ = l_Lean_Syntax_node3(
                v___x_4575_,
                v___x_4580_,
                v___x_4582_,
                v___x_4600_,
                v___x_4587_,
            );
            v___x_4602_ = l_Lean_Parser_Tactic_Grind_skip___closed__0;
            v___x_4603_ = l_Lean_Parser_Tactic_Grind_skip___closed__1;
            v___x_4604_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_4604_, 0, v___x_4575_);
            lean_ctor_set(v___x_4604_, 1, v___x_4602_);
            v___x_4605_ = l_Lean_Syntax_node1(v___x_4575_, v___x_4603_, v___x_4604_);
            v___x_4606_ = l_Lean_Syntax_node2(v___x_4575_, v___x_4584_, v___x_4605_, v___x_4590_);
            v___x_4607_ = l_Lean_Syntax_node1(v___x_4575_, v___x_4579_, v___x_4606_);
            v___x_4608_ = l_Lean_Syntax_node1(v___x_4575_, v___x_4583_, v___x_4607_);
            v___x_4609_ = l_Lean_Syntax_node1(v___x_4575_, v___x_4569_, v___x_4608_);
            v___x_4610_ = l_Lean_Syntax_node3(
                v___x_4575_,
                v___x_4580_,
                v___x_4582_,
                v___x_4609_,
                v___x_4587_,
            );
            v___x_4611_ = l_Lean_Syntax_node2(v___x_4575_, v___x_4579_, v___x_4601_, v___x_4610_);
            v___x_4612_ = l_Lean_Syntax_node2(v___x_4575_, v___x_4577_, v___x_4578_, v___x_4611_);
            v___x_4613_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_4613_, 0, v___x_4612_);
            lean_ctor_set(v___x_4613_, 1, v_a_4562_);
            return v___x_4613_;
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1___boxed(
    mut v_x_4614_: *mut LeanObject,
    mut v_a_4615_: *mut LeanObject,
    mut v_a_4616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4617_: *mut LeanObject = core::ptr::null_mut();
    v_res_4617_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindRepeat____1(v_x_4614_, v_a_4615_, v_a_4616_);
    lean_dec_ref(v_a_4615_);
    return v_res_4617_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5() -> *mut LeanObject {
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    v___x_4633_ = l_Lean_binderIdent;
    v___x_4634_ = l_Lean_Parser_Tactic_Grind_renameI___closed__4;
    v___x_4635_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4636_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4636_, 0, v___x_4635_);
    lean_ctor_set(v___x_4636_, 1, v___x_4634_);
    lean_ctor_set(v___x_4636_, 2, v___x_4633_);
    return v___x_4636_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_renameI___closed__6() -> *mut LeanObject {
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    v___x_4637_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__5_once),
        _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5,
    );
    v___x_4638_ = l_Lean_Parser_Tactic_Grind_first___closed__7;
    v___x_4639_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4639_, 0, v___x_4638_);
    lean_ctor_set(v___x_4639_, 1, v___x_4637_);
    return v___x_4639_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_renameI___closed__7() -> *mut LeanObject {
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    v___x_4640_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__6_once),
        _init_l_Lean_Parser_Tactic_Grind_renameI___closed__6,
    );
    v___x_4641_ = l_Lean_Parser_Tactic_Grind_renameI___closed__3;
    v___x_4642_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4643_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4643_, 0, v___x_4642_);
    lean_ctor_set(v___x_4643_, 1, v___x_4641_);
    lean_ctor_set(v___x_4643_, 2, v___x_4640_);
    return v___x_4643_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_renameI___closed__8() -> *mut LeanObject {
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    v___x_4644_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__7_once),
        _init_l_Lean_Parser_Tactic_Grind_renameI___closed__7,
    );
    v___x_4645_ = lean_unsigned_to_nat(1022);
    v___x_4646_ = l_Lean_Parser_Tactic_Grind_renameI___closed__1;
    v___x_4647_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4647_, 0, v___x_4646_);
    lean_ctor_set(v___x_4647_, 1, v___x_4645_);
    lean_ctor_set(v___x_4647_, 2, v___x_4644_);
    return v___x_4647_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_renameI() -> *mut LeanObject {
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    v___x_4648_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__8_once),
        _init_l_Lean_Parser_Tactic_Grind_renameI___closed__8,
    );
    return v___x_4648_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__4() -> *mut LeanObject {
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    v___x_4742_ = l_Lean_Parser_Tactic_configItem;
    v___x_4743_ = l_Lean_Parser_Tactic_Grind_first___closed__7;
    v___x_4744_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4744_, 0, v___x_4743_);
    lean_ctor_set(v___x_4744_, 1, v___x_4742_);
    return v___x_4744_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__5() -> *mut LeanObject {
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    v___x_4745_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__4_once),
        _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__4,
    );
    v___x_4746_ = l_Lean_Parser_Tactic_Grind_setConfig___closed__3;
    v___x_4747_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4748_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4748_, 0, v___x_4747_);
    lean_ctor_set(v___x_4748_, 1, v___x_4746_);
    lean_ctor_set(v___x_4748_, 2, v___x_4745_);
    return v___x_4748_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__6() -> *mut LeanObject {
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    v___x_4749_ = l_Lean_Parser_Tactic_Grind_setOption___closed__18;
    v___x_4750_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__5_once),
        _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__5,
    );
    v___x_4751_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4752_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4752_, 0, v___x_4751_);
    lean_ctor_set(v___x_4752_, 1, v___x_4750_);
    lean_ctor_set(v___x_4752_, 2, v___x_4749_);
    return v___x_4752_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__7() -> *mut LeanObject {
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    v___x_4753_ = l_Lean_Parser_Tactic_Grind_grindSeq;
    v___x_4754_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__6_once),
        _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__6,
    );
    v___x_4755_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4756_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4756_, 0, v___x_4755_);
    lean_ctor_set(v___x_4756_, 1, v___x_4754_);
    lean_ctor_set(v___x_4756_, 2, v___x_4753_);
    return v___x_4756_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__8() -> *mut LeanObject {
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    v___x_4757_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__7_once),
        _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__7,
    );
    v___x_4758_ = lean_unsigned_to_nat(1022);
    v___x_4759_ = l_Lean_Parser_Tactic_Grind_setConfig___closed__1;
    v___x_4760_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4760_, 0, v___x_4759_);
    lean_ctor_set(v___x_4760_, 1, v___x_4758_);
    lean_ctor_set(v___x_4760_, 2, v___x_4757_);
    return v___x_4760_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_setConfig() -> *mut LeanObject {
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    v___x_4761_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_setConfig___closed__8_once),
        _init_l_Lean_Parser_Tactic_Grind_setConfig___closed__8,
    );
    return v___x_4761_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25() -> *mut LeanObject {
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    v___x_4887_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_renameI___closed__5_once),
        _init_l_Lean_Parser_Tactic_Grind_renameI___closed__5,
    );
    v___x_4888_ = l_Lean_Parser_Tactic_Grind_finish___closed__4;
    v___x_4889_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4889_, 0, v___x_4888_);
    lean_ctor_set(v___x_4889_, 1, v___x_4887_);
    return v___x_4889_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__26() -> *mut LeanObject {
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    v___x_4890_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntro___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once),
        _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25,
    );
    v___x_4891_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__24;
    v___x_4892_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4893_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4893_, 0, v___x_4892_);
    lean_ctor_set(v___x_4893_, 1, v___x_4891_);
    lean_ctor_set(v___x_4893_, 2, v___x_4890_);
    return v___x_4893_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__27() -> *mut LeanObject {
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    v___x_4894_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntro___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntro___closed__26_once),
        _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__26,
    );
    v___x_4895_ = lean_unsigned_to_nat(1022);
    v___x_4896_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__1;
    v___x_4897_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4897_, 0, v___x_4896_);
    lean_ctor_set(v___x_4897_, 1, v___x_4895_);
    lean_ctor_set(v___x_4897_, 2, v___x_4894_);
    return v___x_4897_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_symIntro() -> *mut LeanObject {
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    v___x_4898_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntro___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntro___closed__27_once),
        _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__27,
    );
    return v___x_4898_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6() -> *mut LeanObject {
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    v___x_4917_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntro___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntro___closed__25_once),
        _init_l_Lean_Parser_Tactic_Grind_symIntro___closed__25,
    );
    v___x_4918_ = l_Lean_Parser_Tactic_Grind_symIntroLight___closed__5;
    v___x_4919_ = l_Lean_Parser_Tactic_anchor___closed__6;
    v___x_4920_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4920_, 0, v___x_4919_);
    lean_ctor_set(v___x_4920_, 1, v___x_4918_);
    lean_ctor_set(v___x_4920_, 2, v___x_4917_);
    return v___x_4920_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7() -> *mut LeanObject {
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    v___x_4921_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6_once),
        _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__6,
    );
    v___x_4922_ = lean_unsigned_to_nat(1022);
    v___x_4923_ = l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1;
    v___x_4924_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4924_, 0, v___x_4923_);
    lean_ctor_set(v___x_4924_, 1, v___x_4922_);
    lean_ctor_set(v___x_4924_, 2, v___x_4921_);
    return v___x_4924_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Grind_symIntroLight() -> *mut LeanObject {
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    v___x_4925_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7_once),
        _init_l_Lean_Parser_Tactic_Grind_symIntroLight___closed__7,
    );
    return v___x_4925_;
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1(
    mut v_x_4927_: *mut LeanObject,
    mut v_a_4928_: *mut LeanObject,
    mut v_a_4929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: u8 = 0;
    v___x_4930_ = l_Lean_Parser_Tactic_Grind_symIntroLight___closed__1;
    lean_inc(v_x_4927_);
    v___x_4931_ = l_Lean_Syntax_isOfKind(v_x_4927_, v___x_4930_);
    if v___x_4931_ == 0 {
        let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4927_);
        v___x_4932_ = lean_box(1);
        v___x_4933_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4933_, 0, v___x_4932_);
        lean_ctor_set(v___x_4933_, 1, v_a_4929_);
        return v___x_4933_;
    } else {
        let mut v_ref_4934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ids_4937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4938_: u8 = 0;
        let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4934_ = lean_ctor_get(v_a_4928_, 5);
        v___x_4935_ = lean_unsigned_to_nat(2);
        v___x_4936_ = l_Lean_Syntax_getArg(v_x_4927_, v___x_4935_);
        lean_dec(v_x_4927_);
        v_ids_4937_ = l_Lean_Syntax_getArgs(v___x_4936_);
        lean_dec(v___x_4936_);
        v___x_4938_ = 0;
        v___x_4939_ = l_Lean_SourceInfo_fromRef(v_ref_4934_, v___x_4938_);
        v___x_4940_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__1;
        v___x_4941_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__2;
        lean_inc_n(v___x_4939_, 9);
        v___x_4942_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4942_, 0, v___x_4939_);
        lean_ctor_set(v___x_4942_, 1, v___x_4941_);
        v___x_4943_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1;
        v___x_4944_ = l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2;
        v___x_4945_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4945_, 0, v___x_4939_);
        lean_ctor_set(v___x_4945_, 1, v___x_4944_);
        v___x_4946_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__5;
        v___x_4947_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4947_, 0, v___x_4939_);
        lean_ctor_set(v___x_4947_, 1, v___x_4946_);
        v___x_4948_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0;
        v___x_4949_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4949_, 0, v___x_4939_);
        lean_ctor_set(v___x_4949_, 1, v___x_4948_);
        v___x_4950_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__16;
        v___x_4951_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__17;
        v___x_4952_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4952_, 0, v___x_4939_);
        lean_ctor_set(v___x_4952_, 1, v___x_4950_);
        v___x_4953_ = l_Lean_Syntax_node1(v___x_4939_, v___x_4951_, v___x_4952_);
        v___x_4954_ = l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9;
        v___x_4955_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4955_, 0, v___x_4939_);
        lean_ctor_set(v___x_4955_, 1, v___x_4954_);
        v___x_4956_ = l_Lean_Syntax_node5(
            v___x_4939_,
            v___x_4943_,
            v___x_4945_,
            v___x_4947_,
            v___x_4949_,
            v___x_4953_,
            v___x_4955_,
        );
        v___x_4957_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3_once), _init_l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__3);
        v___x_4958_ = l_Array_appendCore___redArg(v___x_4957_, v_ids_4937_);
        lean_dec_ref(v_ids_4937_);
        v___x_4959_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_4959_, 0, v___x_4939_);
        lean_ctor_set(v___x_4959_, 1, v___x_4943_);
        lean_ctor_set(v___x_4959_, 2, v___x_4958_);
        v___x_4960_ = l_Lean_Syntax_node3(
            v___x_4939_,
            v___x_4940_,
            v___x_4942_,
            v___x_4956_,
            v___x_4959_,
        );
        v___x_4961_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4961_, 0, v___x_4960_);
        lean_ctor_set(v___x_4961_, 1, v_a_4929_);
        return v___x_4961_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___boxed(
    mut v_x_4962_: *mut LeanObject,
    mut v_a_4963_: *mut LeanObject,
    mut v_a_4964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4965_: *mut LeanObject = core::ptr::null_mut();
    v_res_4965_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1(v_x_4962_, v_a_4963_, v_a_4964_);
    lean_dec_ref(v_a_4963_);
    return v_res_4965_;
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1(
    mut v_x_5006_: *mut LeanObject,
    mut v_a_5007_: *mut LeanObject,
    mut v_a_5008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: u8 = 0;
    v___x_5009_ = l_Lean_Parser_Tactic_Grind_symIntrosLight___closed__1;
    v___x_5010_ = l_Lean_Syntax_isOfKind(v_x_5006_, v___x_5009_);
    if v___x_5010_ == 0 {
        let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
        v___x_5011_ = lean_box(1);
        v___x_5012_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5012_, 0, v___x_5011_);
        lean_ctor_set(v___x_5012_, 1, v_a_5008_);
        return v___x_5012_;
    } else {
        let mut v_ref_5013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5014_: u8 = 0;
        let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
        v_ref_5013_ = lean_ctor_get(v_a_5007_, 5);
        v___x_5014_ = 0;
        v___x_5015_ = l_Lean_SourceInfo_fromRef(v_ref_5013_, v___x_5014_);
        v___x_5016_ = l_Lean_Parser_Tactic_Grind_symIntros___closed__1;
        v___x_5017_ = l_Lean_Parser_Tactic_Grind_symIntros___closed__2;
        lean_inc_n(v___x_5015_, 8);
        v___x_5018_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5018_, 0, v___x_5015_);
        lean_ctor_set(v___x_5018_, 1, v___x_5017_);
        v___x_5019_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1;
        v___x_5020_ = l_Lean_Parser_Tactic_Grind_grind__filter_x28___x29___closed__2;
        v___x_5021_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5021_, 0, v___x_5015_);
        lean_ctor_set(v___x_5021_, 1, v___x_5020_);
        v___x_5022_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__5;
        v___x_5023_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5023_, 0, v___x_5015_);
        lean_ctor_set(v___x_5023_, 1, v___x_5022_);
        v___x_5024_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntroLight__1___closed__0;
        v___x_5025_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5025_, 0, v___x_5015_);
        lean_ctor_set(v___x_5025_, 1, v___x_5024_);
        v___x_5026_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__16;
        v___x_5027_ = l_Lean_Parser_Tactic_Grind_symIntro___closed__17;
        v___x_5028_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5028_, 0, v___x_5015_);
        lean_ctor_set(v___x_5028_, 1, v___x_5026_);
        v___x_5029_ = l_Lean_Syntax_node1(v___x_5015_, v___x_5027_, v___x_5028_);
        v___x_5030_ = l_Lean_Parser_Tactic_Grind_grind__filter_quot___closed__9;
        v___x_5031_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5031_, 0, v___x_5015_);
        lean_ctor_set(v___x_5031_, 1, v___x_5030_);
        v___x_5032_ = l_Lean_Syntax_node5(
            v___x_5015_,
            v___x_5019_,
            v___x_5021_,
            v___x_5023_,
            v___x_5025_,
            v___x_5029_,
            v___x_5031_,
        );
        v___x_5033_ = l_Lean_Syntax_node2(v___x_5015_, v___x_5016_, v___x_5018_, v___x_5032_);
        v___x_5034_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5034_, 0, v___x_5033_);
        lean_ctor_set(v___x_5034_, 1, v_a_5008_);
        return v___x_5034_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1___boxed(
    mut v_x_5035_: *mut LeanObject,
    mut v_a_5036_: *mut LeanObject,
    mut v_a_5037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5038_: *mut LeanObject = core::ptr::null_mut();
    v_res_5038_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__symIntrosLight__1(v_x_5035_, v_a_5036_, v_a_5037_);
    lean_dec_ref(v_a_5036_);
    return v_res_5038_;
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1(
    mut v_x_5252_: *mut LeanObject,
    mut v_a_5253_: *mut LeanObject,
    mut v_a_5254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: u8 = 0;
    v___x_5255_ = l_Lean_Parser_Tactic_Grind_grindExact___00__closed__1;
    lean_inc(v_x_5252_);
    v___x_5256_ = l_Lean_Syntax_isOfKind(v_x_5252_, v___x_5255_);
    if v___x_5256_ == 0 {
        let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5252_);
        v___x_5257_ = lean_box(1);
        v___x_5258_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5258_, 0, v___x_5257_);
        lean_ctor_set(v___x_5258_, 1, v_a_5254_);
        return v___x_5258_;
    } else {
        let mut v_ref_5259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5262_: u8 = 0;
        let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
        v_ref_5259_ = lean_ctor_get(v_a_5253_, 5);
        v___x_5260_ = lean_unsigned_to_nat(1);
        v___x_5261_ = l_Lean_Syntax_getArg(v_x_5252_, v___x_5260_);
        lean_dec(v_x_5252_);
        v___x_5262_ = 0;
        v___x_5263_ = l_Lean_SourceInfo_fromRef(v_ref_5259_, v___x_5262_);
        v___x_5264_ = l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__1;
        v___x_5265_ = l_Lean_Parser_Tactic_Grind_nestedTacticCore___closed__2;
        lean_inc_n(v___x_5263_, 7);
        v___x_5266_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5266_, 0, v___x_5263_);
        lean_ctor_set(v___x_5266_, 1, v___x_5265_);
        v___x_5267_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grind_xb7____1___closed__0;
        v___x_5268_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5268_, 0, v___x_5263_);
        lean_ctor_set(v___x_5268_, 1, v___x_5267_);
        v___x_5269_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__0;
        v___x_5270_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__2;
        v___x_5271_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__use__1___closed__1;
        v___x_5272_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__3;
        v___x_5273_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___closed__4;
        v___x_5274_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5274_, 0, v___x_5263_);
        lean_ctor_set(v___x_5274_, 1, v___x_5272_);
        v___x_5275_ = l_Lean_Syntax_node2(v___x_5263_, v___x_5273_, v___x_5274_, v___x_5261_);
        v___x_5276_ = l_Lean_Syntax_node1(v___x_5263_, v___x_5271_, v___x_5275_);
        v___x_5277_ = l_Lean_Syntax_node1(v___x_5263_, v___x_5270_, v___x_5276_);
        v___x_5278_ = l_Lean_Syntax_node1(v___x_5263_, v___x_5269_, v___x_5277_);
        v___x_5279_ = l_Lean_Syntax_node3(
            v___x_5263_,
            v___x_5264_,
            v___x_5266_,
            v___x_5268_,
            v___x_5278_,
        );
        v___x_5280_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5280_, 0, v___x_5279_);
        lean_ctor_set(v___x_5280_, 1, v_a_5254_);
        return v___x_5280_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1___boxed(
    mut v_x_5281_: *mut LeanObject,
    mut v_a_5282_: *mut LeanObject,
    mut v_a_5283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5284_: *mut LeanObject = core::ptr::null_mut();
    v_res_5284_ = l_Lean_Parser_Tactic_Grind___aux__Init__Grind__Interactive______macroRules__Lean__Parser__Tactic__Grind__grindExact____1(v_x_5281_, v_a_5282_, v_a_5283_);
    lean_dec_ref(v_a_5282_);
    return v_res_5284_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Interactive(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Interactive(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Tactic_grindLemma = _init_l_Lean_Parser_Tactic_grindLemma();
    lean_mark_persistent(l_Lean_Parser_Tactic_grindLemma);
    l_Lean_Parser_Tactic_grindLemmaMin = _init_l_Lean_Parser_Tactic_grindLemmaMin();
    lean_mark_persistent(l_Lean_Parser_Tactic_grindLemmaMin);
    l_Lean_Parser_Tactic_grindParam = _init_l_Lean_Parser_Tactic_grindParam();
    lean_mark_persistent(l_Lean_Parser_Tactic_grindParam);
    l_Lean_Parser_Category_grind__filter = _init_l_Lean_Parser_Category_grind__filter();
    lean_mark_persistent(l_Lean_Parser_Category_grind__filter);
    l_Lean_Parser_Category_grind = _init_l_Lean_Parser_Category_grind();
    lean_mark_persistent(l_Lean_Parser_Category_grind);
    l_Lean_Parser_Tactic_Grind_thm = _init_l_Lean_Parser_Tactic_Grind_thm();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_thm);
    l_Lean_Parser_Tactic_Grind_instantiate = _init_l_Lean_Parser_Tactic_Grind_instantiate();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_instantiate);
    l_Lean_Parser_Tactic_Grind_use = _init_l_Lean_Parser_Tactic_Grind_use();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_use);
    l_Lean_Parser_Category_grind__ref = _init_l_Lean_Parser_Category_grind__ref();
    lean_mark_persistent(l_Lean_Parser_Category_grind__ref);
    l_Lean_Parser_Tactic_Grind_finish = _init_l_Lean_Parser_Tactic_Grind_finish();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_finish);
    l_Lean_Parser_Tactic_Grind_finishTrace = _init_l_Lean_Parser_Tactic_Grind_finishTrace();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_finishTrace);
    l_Lean_Parser_Tactic_Grind_next = _init_l_Lean_Parser_Tactic_Grind_next();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_next);
    l_Lean_Parser_Tactic_Grind_renameI = _init_l_Lean_Parser_Tactic_Grind_renameI();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_renameI);
    l_Lean_Parser_Tactic_Grind_setConfig = _init_l_Lean_Parser_Tactic_Grind_setConfig();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_setConfig);
    l_Lean_Parser_Tactic_Grind_symIntro = _init_l_Lean_Parser_Tactic_Grind_symIntro();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_symIntro);
    l_Lean_Parser_Tactic_Grind_symIntroLight = _init_l_Lean_Parser_Tactic_Grind_symIntroLight();
    lean_mark_persistent(l_Lean_Parser_Tactic_Grind_symIntroLight);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Interactive(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Interactive(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Interactive(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Interactive(builtin);
}
