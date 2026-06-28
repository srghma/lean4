// Lean compiler output
// Module: Init.Grind.Attr
// Imports: Init.Tactics
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_simpPost, l_Lean_Parser_Tactic_simpPre,
    runtime_initialize_Init_Tactics,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_unsigned_to_nat,
};
pub static l_Lean_Parser_resetGrindAttrs___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__2_value: LeanStringObject<16> =
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
            114, 101, 115, 101, 116, 71, 114, 105, 110, 100, 65, 116, 116, 114, 115, 0,
        ],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_resetGrindAttrs___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_resetGrindAttrs___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_resetGrindAttrs___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__2_value) as *mut LeanObject,
        10802873928890743578 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_resetGrindAttrs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__4_value: LeanStringObject<19> =
    LeanStringObject {
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
            114, 101, 115, 101, 116, 95, 103, 114, 105, 110, 100, 95, 97, 116, 116, 114, 115, 37, 0,
        ],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_resetGrindAttrs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__3_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_resetGrindAttrs___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_resetGrindAttrs: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 114, 105, 110, 100, 71, 101, 110, 0],
};
static mut l_Lean_Parser_Attr_grindGen___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__1_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [65, 116, 116, 114, 0],
};
static mut l_Lean_Parser_Attr_grindGen___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindGen___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindGen___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindGen___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindGen___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__0_value) as *mut LeanObject,
        9714501210324126650 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindGen___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__3_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lean_Parser_Attr_grindGen___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__3_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindGen___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__5_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lean_Parser_Attr_grindGen___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__5_value) as *mut LeanObject,
        17761616517784022991 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindGen___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__6_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindGen___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__8_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Lean_Parser_Attr_grindGen___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__8_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindGen___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindGen___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindGen___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__11_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindGen: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [103, 114, 105, 110, 100, 69, 113, 0],
};
static mut l_Lean_Parser_Attr_grindEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindEq___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindEq___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindEq___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindEq___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__0_value) as *mut LeanObject,
        14718087869874512563 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [61, 0],
};
static mut l_Lean_Parser_Attr_grindEq___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindEq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__4_value: LeanStringObject<9> = LeanStringObject {
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
static mut l_Lean_Parser_Attr_grindEq___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__4_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEq___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEq___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEq___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEq___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindEq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__0_value: LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 69, 113, 82, 104, 115, 0],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindEqRhs___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__0_value) as *mut LeanObject,
        4956164565610314718 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqRhs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__2_value: LeanStringObject<7> =
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
        m_data: [97, 116, 111, 109, 105, 99, 0],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__2_value) as *mut LeanObject,
        4024150434455327032 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqRhs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__4_value: LeanStringObject<2> =
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
        m_data: [95, 0],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqRhs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqRhs___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqRhs___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqRhs___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqRhs___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindEqRhs: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__0_value: LeanStringObject<12> =
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
        m_data: [103, 114, 105, 110, 100, 69, 113, 66, 111, 116, 104, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBoth___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindEqBoth___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__0_value) as *mut LeanObject,
        9254304300027733583 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBoth___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBoth___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBoth___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBoth___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBoth___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBoth___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindEqBoth: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__0_value: LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 69, 113, 66, 119, 100, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindEqBwd___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__0_value) as *mut LeanObject,
        3844513800486599162 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__2_value: LeanStringObject<14> =
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
            112, 97, 116, 116, 101, 114, 110, 73, 103, 110, 111, 114, 101, 0,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__2_value) as *mut LeanObject,
        17328449285856252867 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__4_value: LeanStringObject<7> =
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
static mut l_Lean_Parser_Attr_grindEqBwd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__4_value) as *mut LeanObject,
        393173242845875278 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__6_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Attr_grindEqBwd___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__6_value) as *mut LeanObject,
        2214559063752339918 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__8_value: LeanStringObject<4> =
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
        m_data: [226, 134, 144, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__12_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__13_value: LeanStringObject<3> =
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
        m_data: [60, 45, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__14_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__14_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__16_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__17_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__18_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__17_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__18_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__19_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__18_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__19_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__20_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindEqBwd___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__20_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindEqBwd: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 114, 105, 110, 100, 66, 119, 100, 0],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindBwd___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__0_value) as *mut LeanObject,
        1689458581469504370 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__2_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lean_Parser_Attr_grindBwd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindBwd___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindBwd___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__8_value) as *mut LeanObject,
        9149852190130109334 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__4_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindBwd___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindBwd___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__5_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__13_value) as *mut LeanObject,
        1297364225897356313 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__13_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindBwd___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__10_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindBwd: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 114, 105, 110, 100, 70, 119, 100, 0],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindFwd___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__0_value) as *mut LeanObject,
        3412781221517828473 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 134, 146, 0],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindFwd___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindFwd___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__2_value) as *mut LeanObject,
        11707734540142241164 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__6_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 62, 0],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__6_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindFwd___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindFwd___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__6_value) as *mut LeanObject,
        9958343667474391476 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__6_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFwd___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__12_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindFwd: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [103, 114, 105, 110, 100, 82, 76, 0],
};
static mut l_Lean_Parser_Attr_grindRL___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindRL___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindRL___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindRL___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindRL___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__0_value) as *mut LeanObject,
        14783791908340461652 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindRL___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 135, 144, 0],
};
static mut l_Lean_Parser_Attr_grindRL___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindRL___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindRL___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__2_value) as *mut LeanObject,
        17529940758261935356 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindRL___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindRL___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindRL___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__6_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [60, 61, 0],
};
static mut l_Lean_Parser_Attr_grindRL___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__6_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindRL___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindRL___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__6_value) as *mut LeanObject,
        8722646758108166465 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindRL___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__6_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindRL___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindRL___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindRL___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindRL___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindRL___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__12_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindRL: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [103, 114, 105, 110, 100, 76, 82, 0],
};
static mut l_Lean_Parser_Attr_grindLR___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindLR___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindLR___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindLR___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindLR___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__0_value) as *mut LeanObject,
        11844982159682858904 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindLR___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 135, 146, 0],
};
static mut l_Lean_Parser_Attr_grindLR___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindLR___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindLR___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__2_value) as *mut LeanObject,
        17456214878486818065 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindLR___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindLR___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindLR___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__6_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [61, 62, 0],
};
static mut l_Lean_Parser_Attr_grindLR___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__6_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindLR___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindLR___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__6_value) as *mut LeanObject,
        5713651635530161729 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindLR___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__6_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindLR___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindLR___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindLR___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindLR___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindLR___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__12_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindLR: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 114, 105, 110, 100, 68, 101, 102, 0],
};
static mut l_Lean_Parser_Attr_grindDef___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindDef___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindDef___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindDef___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindDef___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__0_value) as *mut LeanObject,
        5549592694638828098 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindDef___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__2_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lean_Parser_Attr_grindDef___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindDef___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindDef___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__2_value) as *mut LeanObject,
        2511666537814787754 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindDef___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindDef___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindDef___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__6_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 1,
    m_data: [194, 183, 0],
};
static mut l_Lean_Parser_Attr_grindDef___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__6_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindDef___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindDef___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__6_value) as *mut LeanObject,
        16697830463868302406 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindDef___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__6_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Attr_grindDef___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindDef___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindDef___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindDef___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindDef___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindDef___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__13_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindDef: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindUsr___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 114, 105, 110, 100, 85, 115, 114, 0],
};
static mut l_Lean_Parser_Attr_grindUsr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindUsr___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__0_value) as *mut LeanObject,
        1329309285596805836 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindUsr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindUsr___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 115, 114, 0],
};
static mut l_Lean_Parser_Attr_grindUsr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindUsr___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindUsr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindUsr___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindUsr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindUsr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCases___closed__0_value: LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 67, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Parser_Attr_grindCases___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindCases___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindCases___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindCases___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindCases___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__0_value) as *mut LeanObject,
        11737843193706483285 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindCases___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCases___closed__2_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Attr_grindCases___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCases___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindCases___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCases___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindCases___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindCases: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__0_value: LeanStringObject<16> =
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
            103, 114, 105, 110, 100, 67, 97, 115, 101, 115, 69, 97, 103, 101, 114, 0,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
            4584992172905639687 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindCasesEager___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__0_value)
                as *mut LeanObject,
            5084203056696709707 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__2_value: LeanStringObject<6> =
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
        m_data: [101, 97, 103, 101, 114, 0],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__3_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindCasesEager: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindIntro___closed__0_value: LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 73, 110, 116, 114, 111, 0],
    };
static mut l_Lean_Parser_Attr_grindIntro___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindIntro___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__0_value) as *mut LeanObject,
        9959989771779604110 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindIntro___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindIntro___closed__2_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Attr_grindIntro___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindIntro___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindIntro___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindIntro___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindIntro___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindIntro: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindExt___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 114, 105, 110, 100, 69, 120, 116, 0],
};
static mut l_Lean_Parser_Attr_grindExt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindExt___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindExt___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindExt___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindExt___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__0_value) as *mut LeanObject,
        18276616586504290707 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindExt___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindExt___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [101, 120, 116, 0],
};
static mut l_Lean_Parser_Attr_grindExt___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindExt___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindExt___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindExt___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindExt___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindExt: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindInj___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 114, 105, 110, 100, 73, 110, 106, 0],
};
static mut l_Lean_Parser_Attr_grindInj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindInj___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindInj___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindInj___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindInj___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__0_value) as *mut LeanObject,
        13947935108849328607 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindInj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindInj___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 110, 106, 0],
};
static mut l_Lean_Parser_Attr_grindInj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindInj___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindInj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindInj___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindInj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindInj: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFunCC___closed__0_value: LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 70, 117, 110, 67, 67, 0],
    };
static mut l_Lean_Parser_Attr_grindFunCC___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindFunCC___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__0_value) as *mut LeanObject,
        3120519524940125401 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFunCC___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFunCC___closed__2_value: LeanStringObject<6> =
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
        m_data: [102, 117, 110, 67, 67, 0],
    };
static mut l_Lean_Parser_Attr_grindFunCC___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFunCC___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFunCC___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindFunCC___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindFunCC___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindFunCC: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__0_value: LeanStringObject<10> =
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
        m_data: [103, 114, 105, 110, 100, 78, 111, 114, 109, 0],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindNorm___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__0_value) as *mut LeanObject,
        10672965319075724966 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 111, 114, 109, 0],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_grindNorm___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindNorm___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindNorm___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindNorm___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindNorm___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindNorm___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grindNorm___closed__7_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_grindNorm___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__7_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindNorm___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindNorm___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__8_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__7_value) as *mut LeanObject,
        5265644217102624940 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__11_value: LeanStringObject<4> =
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
        m_data: [60, 45, 32, 0],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__11_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindNorm___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value) as *mut LeanObject,
        9392652980833654105 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindNorm___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__12_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__11_value) as *mut LeanObject,
        11081745058534201334 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__13_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__16_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__17_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindNorm___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__17_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_grindNorm___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindNorm___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindNorm___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindNorm___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grindNorm: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grindUnfold___closed__0_value: LeanStringObject<12> =
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
        m_data: [103, 114, 105, 110, 100, 85, 110, 102, 111, 108, 100, 0],
    };
static mut l_Lean_Parser_Attr_grindUnfold___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindUnfold___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__0_value) as *mut LeanObject,
        15827030602716394966 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindUnfold___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindUnfold___closed__2_value: LeanStringObject<7> =
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
        m_data: [117, 110, 102, 111, 108, 100, 0],
    };
static mut l_Lean_Parser_Attr_grindUnfold___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindUnfold___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindUnfold___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindUnfold___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindUnfold___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindUnfold: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 114, 105, 110, 100, 83, 121, 109, 0],
};
static mut l_Lean_Parser_Attr_grindSym___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindSym___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindSym___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindSym___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindSym___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__0_value) as *mut LeanObject,
        1728939392783600744 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindSym___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 121, 109, 98, 111, 108, 0],
};
static mut l_Lean_Parser_Attr_grindSym___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindSym___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindSym___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__5_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_grindSym___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__5_value) as *mut LeanObject,
        17836958171642591098 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindSym___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__6_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindSym___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindSym___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindSym___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Attr_grindSym: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindMod___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 114, 105, 110, 100, 77, 111, 100, 0],
};
static mut l_Lean_Parser_Attr_grindMod___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grindMod___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindMod___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grindMod___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grindMod___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__0_value) as *mut LeanObject,
        8580387018487626918 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindMod___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grindMod___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grindMod___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_grindMod___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grindMod___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grindMod: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grind___closed__0_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lean_Parser_Attr_grind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grind___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grind___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grind___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__0_value) as *mut LeanObject,
        6111248473341059083 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grind___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grind___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_grind___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grind: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grind_x21___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [103, 114, 105, 110, 100, 33, 0],
};
static mut l_Lean_Parser_Attr_grind_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grind_x21___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__0_value) as *mut LeanObject,
        15278515049066527744 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grind_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grind_x21___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grind_x21___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_grind_x21___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind_x21___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind_x21___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind_x21___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grind_x21: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grind_x3f___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [103, 114, 105, 110, 100, 63, 0],
};
static mut l_Lean_Parser_Attr_grind_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
        4584992172905639687 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_grind_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__0_value) as *mut LeanObject,
        14609666066721317603 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grind_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grind_x3f___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grind_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_grind_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind_x3f___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grind_x3f: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grind_x21_x3f___closed__0_value: LeanStringObject<8> =
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
        m_data: [103, 114, 105, 110, 100, 33, 63, 0],
    };
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value) as *mut LeanObject,
            4584992172905639687 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__0_value) as *mut LeanObject,
        12064337937714458527 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_grind_x21_x3f___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grind_x21_x3f: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_genPattern___redArg(mut v_x_776_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_x_776_);
    return v_x_776_;
}
pub unsafe fn l_Lean_Grind_genPattern___redArg___boxed(
    mut v_x_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_778_: *mut LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Lean_Grind_genPattern___redArg(v_x_777_);
    lean_dec(v_x_777_);
    return v_res_778_;
}
pub unsafe fn l_Lean_Grind_genPattern(
    mut v_00_u03b1_779_: *mut LeanObject,
    mut v___h_780_: *mut LeanObject,
    mut v_x_781_: *mut LeanObject,
    mut v___val_782_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_781_);
    return v_x_781_;
}
pub unsafe fn l_Lean_Grind_genPattern___boxed(
    mut v_00_u03b1_783_: *mut LeanObject,
    mut v___h_784_: *mut LeanObject,
    mut v_x_785_: *mut LeanObject,
    mut v___val_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_787_: *mut LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Lean_Grind_genPattern(v_00_u03b1_783_, v___h_784_, v_x_785_, v___val_786_);
    lean_dec(v___val_786_);
    lean_dec(v_x_785_);
    return v_res_787_;
}
pub unsafe fn l_Lean_Grind_genHEqPattern___redArg(
    mut v_x_788_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_788_);
    return v_x_788_;
}
pub unsafe fn l_Lean_Grind_genHEqPattern___redArg___boxed(
    mut v_x_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_790_: *mut LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Lean_Grind_genHEqPattern___redArg(v_x_789_);
    lean_dec(v_x_789_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Grind_genHEqPattern(
    mut v_00_u03b1_791_: *mut LeanObject,
    mut v_00_u03b2_792_: *mut LeanObject,
    mut v___h_793_: *mut LeanObject,
    mut v_x_794_: *mut LeanObject,
    mut v___val_795_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_794_);
    return v_x_794_;
}
pub unsafe fn l_Lean_Grind_genHEqPattern___boxed(
    mut v_00_u03b1_796_: *mut LeanObject,
    mut v_00_u03b2_797_: *mut LeanObject,
    mut v___h_798_: *mut LeanObject,
    mut v_x_799_: *mut LeanObject,
    mut v___val_800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_801_: *mut LeanObject = core::ptr::null_mut();
    v_res_801_ = l_Lean_Grind_genHEqPattern(
        v_00_u03b1_796_,
        v_00_u03b2_797_,
        v___h_798_,
        v_x_799_,
        v___val_800_,
    );
    lean_dec(v___val_800_);
    lean_dec(v_x_799_);
    return v_res_801_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__4() -> *mut LeanObject {
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Parser_Tactic_simpPost;
    v___x_1292_ = l_Lean_Parser_Tactic_simpPre;
    v___x_1293_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1294_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1294_, 0, v___x_1293_);
    lean_ctor_set(v___x_1294_, 1, v___x_1292_);
    lean_ctor_set(v___x_1294_, 2, v___x_1291_);
    return v___x_1294_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__5() -> *mut LeanObject {
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    v___x_1295_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__4_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__4,
    );
    v___x_1296_ = l_Lean_Parser_Attr_grindEq___closed__5;
    v___x_1297_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1297_, 0, v___x_1296_);
    lean_ctor_set(v___x_1297_, 1, v___x_1295_);
    return v___x_1297_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__6() -> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    v___x_1298_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__5_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__5,
    );
    v___x_1299_ = l_Lean_Parser_Attr_grindNorm___closed__3;
    v___x_1300_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1301_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1301_, 0, v___x_1300_);
    lean_ctor_set(v___x_1301_, 1, v___x_1299_);
    lean_ctor_set(v___x_1301_, 2, v___x_1298_);
    return v___x_1301_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__18() -> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Lean_Parser_Attr_grindNorm___closed__17;
    v___x_1333_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__6_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__6,
    );
    v___x_1334_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1335_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1335_, 0, v___x_1334_);
    lean_ctor_set(v___x_1335_, 1, v___x_1333_);
    lean_ctor_set(v___x_1335_, 2, v___x_1332_);
    return v___x_1335_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__19() -> *mut LeanObject {
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    v___x_1336_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__18_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__18,
    );
    v___x_1337_ = l_Lean_Parser_Attr_grindNorm___closed__1;
    v___x_1338_ = l_Lean_Parser_Attr_grindNorm___closed__0;
    v___x_1339_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_1339_, 0, v___x_1338_);
    lean_ctor_set(v___x_1339_, 1, v___x_1337_);
    lean_ctor_set(v___x_1339_, 2, v___x_1336_);
    return v___x_1339_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm() -> *mut LeanObject {
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    v___x_1340_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__19_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__19,
    );
    return v___x_1340_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__3() -> *mut LeanObject {
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    v___x_1395_ = l_Lean_Parser_Attr_grindMod___closed__2;
    v___x_1396_ = l_Lean_Parser_Attr_grindNorm;
    v___x_1397_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1398_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1398_, 0, v___x_1397_);
    lean_ctor_set(v___x_1398_, 1, v___x_1396_);
    lean_ctor_set(v___x_1398_, 2, v___x_1395_);
    return v___x_1398_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__4() -> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    v___x_1399_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__3_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__3,
    );
    v___x_1400_ = l_Lean_Parser_Attr_grindFunCC;
    v___x_1401_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1402_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1402_, 0, v___x_1401_);
    lean_ctor_set(v___x_1402_, 1, v___x_1400_);
    lean_ctor_set(v___x_1402_, 2, v___x_1399_);
    return v___x_1402_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__5() -> *mut LeanObject {
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    v___x_1403_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__4_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__4,
    );
    v___x_1404_ = l_Lean_Parser_Attr_grindInj;
    v___x_1405_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1406_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1406_, 0, v___x_1405_);
    lean_ctor_set(v___x_1406_, 1, v___x_1404_);
    lean_ctor_set(v___x_1406_, 2, v___x_1403_);
    return v___x_1406_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__6() -> *mut LeanObject {
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    v___x_1407_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__5_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__5,
    );
    v___x_1408_ = l_Lean_Parser_Attr_grindSym;
    v___x_1409_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1410_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1410_, 0, v___x_1409_);
    lean_ctor_set(v___x_1410_, 1, v___x_1408_);
    lean_ctor_set(v___x_1410_, 2, v___x_1407_);
    return v___x_1410_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__7() -> *mut LeanObject {
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    v___x_1411_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__6_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__6,
    );
    v___x_1412_ = l_Lean_Parser_Attr_grindGen;
    v___x_1413_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1414_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1414_, 0, v___x_1413_);
    lean_ctor_set(v___x_1414_, 1, v___x_1412_);
    lean_ctor_set(v___x_1414_, 2, v___x_1411_);
    return v___x_1414_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__8() -> *mut LeanObject {
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    v___x_1415_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__7_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__7,
    );
    v___x_1416_ = l_Lean_Parser_Attr_grindExt;
    v___x_1417_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1418_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1418_, 0, v___x_1417_);
    lean_ctor_set(v___x_1418_, 1, v___x_1416_);
    lean_ctor_set(v___x_1418_, 2, v___x_1415_);
    return v___x_1418_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__9() -> *mut LeanObject {
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    v___x_1419_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__8_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__8,
    );
    v___x_1420_ = l_Lean_Parser_Attr_grindIntro;
    v___x_1421_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1422_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1422_, 0, v___x_1421_);
    lean_ctor_set(v___x_1422_, 1, v___x_1420_);
    lean_ctor_set(v___x_1422_, 2, v___x_1419_);
    return v___x_1422_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__10() -> *mut LeanObject {
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1423_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__9_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__9,
    );
    v___x_1424_ = l_Lean_Parser_Attr_grindCases;
    v___x_1425_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1426_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1426_, 0, v___x_1425_);
    lean_ctor_set(v___x_1426_, 1, v___x_1424_);
    lean_ctor_set(v___x_1426_, 2, v___x_1423_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__11() -> *mut LeanObject {
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1427_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__10_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__10,
    );
    v___x_1428_ = l_Lean_Parser_Attr_grindCasesEager;
    v___x_1429_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1430_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1430_, 0, v___x_1429_);
    lean_ctor_set(v___x_1430_, 1, v___x_1428_);
    lean_ctor_set(v___x_1430_, 2, v___x_1427_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__12() -> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__11_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__11,
    );
    v___x_1432_ = l_Lean_Parser_Attr_grindUsr;
    v___x_1433_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1434_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1434_, 0, v___x_1433_);
    lean_ctor_set(v___x_1434_, 1, v___x_1432_);
    lean_ctor_set(v___x_1434_, 2, v___x_1431_);
    return v___x_1434_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__13() -> *mut LeanObject {
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    v___x_1435_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__12_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__12,
    );
    v___x_1436_ = l_Lean_Parser_Attr_grindLR;
    v___x_1437_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1438_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1438_, 0, v___x_1437_);
    lean_ctor_set(v___x_1438_, 1, v___x_1436_);
    lean_ctor_set(v___x_1438_, 2, v___x_1435_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__14() -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___x_1439_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__13_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__13,
    );
    v___x_1440_ = l_Lean_Parser_Attr_grindRL;
    v___x_1441_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1442_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1442_, 0, v___x_1441_);
    lean_ctor_set(v___x_1442_, 1, v___x_1440_);
    lean_ctor_set(v___x_1442_, 2, v___x_1439_);
    return v___x_1442_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__15() -> *mut LeanObject {
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    v___x_1443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__14_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__14,
    );
    v___x_1444_ = l_Lean_Parser_Attr_grindFwd;
    v___x_1445_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1446_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1446_, 0, v___x_1445_);
    lean_ctor_set(v___x_1446_, 1, v___x_1444_);
    lean_ctor_set(v___x_1446_, 2, v___x_1443_);
    return v___x_1446_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__16() -> *mut LeanObject {
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v___x_1447_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__15_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__15,
    );
    v___x_1448_ = l_Lean_Parser_Attr_grindBwd;
    v___x_1449_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1450_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1450_, 0, v___x_1449_);
    lean_ctor_set(v___x_1450_, 1, v___x_1448_);
    lean_ctor_set(v___x_1450_, 2, v___x_1447_);
    return v___x_1450_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__17() -> *mut LeanObject {
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    v___x_1451_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__16_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__16,
    );
    v___x_1452_ = l_Lean_Parser_Attr_grindEqBwd;
    v___x_1453_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1454_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1454_, 0, v___x_1453_);
    lean_ctor_set(v___x_1454_, 1, v___x_1452_);
    lean_ctor_set(v___x_1454_, 2, v___x_1451_);
    return v___x_1454_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__18() -> *mut LeanObject {
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    v___x_1455_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__17_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__17,
    );
    v___x_1456_ = l_Lean_Parser_Attr_grindEq;
    v___x_1457_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1458_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1458_, 0, v___x_1457_);
    lean_ctor_set(v___x_1458_, 1, v___x_1456_);
    lean_ctor_set(v___x_1458_, 2, v___x_1455_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__19() -> *mut LeanObject {
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    v___x_1459_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__18_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__18,
    );
    v___x_1460_ = l_Lean_Parser_Attr_grindEqRhs;
    v___x_1461_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1462_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1462_, 0, v___x_1461_);
    lean_ctor_set(v___x_1462_, 1, v___x_1460_);
    lean_ctor_set(v___x_1462_, 2, v___x_1459_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__20() -> *mut LeanObject {
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__19_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__19,
    );
    v___x_1464_ = l_Lean_Parser_Attr_grindEqBoth;
    v___x_1465_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1466_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1466_, 0, v___x_1465_);
    lean_ctor_set(v___x_1466_, 1, v___x_1464_);
    lean_ctor_set(v___x_1466_, 2, v___x_1463_);
    return v___x_1466_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__21() -> *mut LeanObject {
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    v___x_1467_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__20_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__20,
    );
    v___x_1468_ = l_Lean_Parser_Attr_grindMod___closed__1;
    v___x_1469_ = l_Lean_Parser_Attr_grindMod___closed__0;
    v___x_1470_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_1470_, 0, v___x_1469_);
    lean_ctor_set(v___x_1470_, 1, v___x_1468_);
    lean_ctor_set(v___x_1470_, 2, v___x_1467_);
    return v___x_1470_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod() -> *mut LeanObject {
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    v___x_1471_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__21_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__21,
    );
    return v___x_1471_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind___closed__3() -> *mut LeanObject {
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    v___x_1481_ = l_Lean_Parser_Attr_grindMod;
    v___x_1482_ = l_Lean_Parser_Attr_grindGen___closed__7;
    v___x_1483_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1484_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1484_, 0, v___x_1483_);
    lean_ctor_set(v___x_1484_, 1, v___x_1482_);
    lean_ctor_set(v___x_1484_, 2, v___x_1481_);
    return v___x_1484_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind___closed__4() -> *mut LeanObject {
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    v___x_1485_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__3_once),
        _init_l_Lean_Parser_Attr_grind___closed__3,
    );
    v___x_1486_ = l_Lean_Parser_Attr_grindEq___closed__5;
    v___x_1487_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1487_, 0, v___x_1486_);
    lean_ctor_set(v___x_1487_, 1, v___x_1485_);
    return v___x_1487_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind___closed__5() -> *mut LeanObject {
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    v___x_1488_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4_once),
        _init_l_Lean_Parser_Attr_grind___closed__4,
    );
    v___x_1489_ = l_Lean_Parser_Attr_grind___closed__2;
    v___x_1490_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1491_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1491_, 0, v___x_1490_);
    lean_ctor_set(v___x_1491_, 1, v___x_1489_);
    lean_ctor_set(v___x_1491_, 2, v___x_1488_);
    return v___x_1491_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind___closed__6() -> *mut LeanObject {
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    v___x_1492_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__5_once),
        _init_l_Lean_Parser_Attr_grind___closed__5,
    );
    v___x_1493_ = lean_unsigned_to_nat(1022);
    v___x_1494_ = l_Lean_Parser_Attr_grind___closed__1;
    v___x_1495_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1495_, 0, v___x_1494_);
    lean_ctor_set(v___x_1495_, 1, v___x_1493_);
    lean_ctor_set(v___x_1495_, 2, v___x_1492_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind() -> *mut LeanObject {
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    v___x_1496_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__6_once),
        _init_l_Lean_Parser_Attr_grind___closed__6,
    );
    return v___x_1496_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21___closed__3() -> *mut LeanObject {
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    v___x_1506_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4_once),
        _init_l_Lean_Parser_Attr_grind___closed__4,
    );
    v___x_1507_ = l_Lean_Parser_Attr_grind_x21___closed__2;
    v___x_1508_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1509_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1509_, 0, v___x_1508_);
    lean_ctor_set(v___x_1509_, 1, v___x_1507_);
    lean_ctor_set(v___x_1509_, 2, v___x_1506_);
    return v___x_1509_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21___closed__4() -> *mut LeanObject {
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v___x_1510_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21___closed__3_once),
        _init_l_Lean_Parser_Attr_grind_x21___closed__3,
    );
    v___x_1511_ = lean_unsigned_to_nat(1022);
    v___x_1512_ = l_Lean_Parser_Attr_grind_x21___closed__1;
    v___x_1513_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    lean_ctor_set(v___x_1513_, 1, v___x_1511_);
    lean_ctor_set(v___x_1513_, 2, v___x_1510_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21() -> *mut LeanObject {
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    v___x_1514_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21___closed__4_once),
        _init_l_Lean_Parser_Attr_grind_x21___closed__4,
    );
    return v___x_1514_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    v___x_1524_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4_once),
        _init_l_Lean_Parser_Attr_grind___closed__4,
    );
    v___x_1525_ = l_Lean_Parser_Attr_grind_x3f___closed__2;
    v___x_1526_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1527_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1527_, 0, v___x_1526_);
    lean_ctor_set(v___x_1527_, 1, v___x_1525_);
    lean_ctor_set(v___x_1527_, 2, v___x_1524_);
    return v___x_1527_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x3f___closed__3_once),
        _init_l_Lean_Parser_Attr_grind_x3f___closed__3,
    );
    v___x_1529_ = lean_unsigned_to_nat(1022);
    v___x_1530_ = l_Lean_Parser_Attr_grind_x3f___closed__1;
    v___x_1531_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    lean_ctor_set(v___x_1531_, 1, v___x_1529_);
    lean_ctor_set(v___x_1531_, 2, v___x_1528_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x3f() -> *mut LeanObject {
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    v___x_1532_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x3f___closed__4_once),
        _init_l_Lean_Parser_Attr_grind_x3f___closed__4,
    );
    return v___x_1532_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    v___x_1542_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4_once),
        _init_l_Lean_Parser_Attr_grind___closed__4,
    );
    v___x_1543_ = l_Lean_Parser_Attr_grind_x21_x3f___closed__2;
    v___x_1544_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1545_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1545_, 0, v___x_1544_);
    lean_ctor_set(v___x_1545_, 1, v___x_1543_);
    lean_ctor_set(v___x_1545_, 2, v___x_1542_);
    return v___x_1545_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    v___x_1546_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21_x3f___closed__3_once),
        _init_l_Lean_Parser_Attr_grind_x21_x3f___closed__3,
    );
    v___x_1547_ = lean_unsigned_to_nat(1022);
    v___x_1548_ = l_Lean_Parser_Attr_grind_x21_x3f___closed__1;
    v___x_1549_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1549_, 0, v___x_1548_);
    lean_ctor_set(v___x_1549_, 1, v___x_1547_);
    lean_ctor_set(v___x_1549_, 2, v___x_1546_);
    return v___x_1549_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21_x3f() -> *mut LeanObject {
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    v___x_1550_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21_x3f___closed__4_once),
        _init_l_Lean_Parser_Attr_grind_x21_x3f___closed__4,
    );
    return v___x_1550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Attr_grindNorm = _init_l_Lean_Parser_Attr_grindNorm();
    lean_mark_persistent(l_Lean_Parser_Attr_grindNorm);
    l_Lean_Parser_Attr_grindMod = _init_l_Lean_Parser_Attr_grindMod();
    lean_mark_persistent(l_Lean_Parser_Attr_grindMod);
    l_Lean_Parser_Attr_grind = _init_l_Lean_Parser_Attr_grind();
    lean_mark_persistent(l_Lean_Parser_Attr_grind);
    l_Lean_Parser_Attr_grind_x21 = _init_l_Lean_Parser_Attr_grind_x21();
    lean_mark_persistent(l_Lean_Parser_Attr_grind_x21);
    l_Lean_Parser_Attr_grind_x3f = _init_l_Lean_Parser_Attr_grind_x3f();
    lean_mark_persistent(l_Lean_Parser_Attr_grind_x3f);
    l_Lean_Parser_Attr_grind_x21_x3f = _init_l_Lean_Parser_Attr_grind_x21_x3f();
    lean_mark_persistent(l_Lean_Parser_Attr_grind_x21_x3f);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Attr(builtin);
}
