// Lean compiler output
// Module: Init.Sym.DSimp.DSimprocDSL
// Imports: Init.Tactics
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
};
use crate::r#gen::Init::Tactics::{initialize_Init_Tactics, runtime_initialize_Init_Tactics};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent,
};
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__2_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__3_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__3_value)
        as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__3_value)
                as *mut LeanObject,
            5855146430765573009 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__5_value: LeanStringObject<13> =
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
        m_data: [115, 121, 109, 95, 100, 115, 105, 109, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__5_value)
        as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__6_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__5_value)
                as *mut LeanObject,
            3020423846782789775 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__3_value)
                as *mut LeanObject,
            10281169276005335805 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__7_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__7_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__9_value: LeanStringObject<17> =
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
            96, 40, 115, 121, 109, 95, 100, 115, 105, 109, 112, 114, 111, 99, 124, 32, 0,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__10_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__5_value)
                as *mut LeanObject,
            3020423846782789775 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__12_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__11_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__13_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__14_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__6_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__18_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__18_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Category_sym__dsimproc: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Sym_DSimp_none___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 121, 109, 0],
};
static mut l_Lean_Parser_Sym_DSimp_none___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_none___closed__1_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [68, 83, 105, 109, 112, 0],
};
static mut l_Lean_Parser_Sym_DSimp_none___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_none___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Lean_Parser_Sym_DSimp_none___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_none___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_none___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_none___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_none___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__3_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
        14634483482441683967 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_DSimp_none___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__3_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__2_value) as *mut LeanObject,
        10522018292007760565 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_none___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_none___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_none___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_none___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__3_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_none___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_none: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_ground___closed__0_value: LeanStringObject<7> =
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
        m_data: [103, 114, 111, 117, 110, 100, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_ground___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_ground___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_ground___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_ground___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_ground___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
        14634483482441683967 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_DSimp_ground___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__0_value) as *mut LeanObject,
        16320649819692919556 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_ground___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_ground___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_ground___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_ground___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_ground___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_ground: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_ground___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_beta___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [98, 101, 116, 97, 0],
};
static mut l_Lean_Parser_Sym_DSimp_beta___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_beta___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_beta___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_beta___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_beta___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
        14634483482441683967 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_DSimp_beta___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__0_value) as *mut LeanObject,
        154037570533536172 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_beta___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_beta___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_beta___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_beta___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_beta___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_beta: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_beta___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_zeta___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [122, 101, 116, 97, 0],
};
static mut l_Lean_Parser_Sym_DSimp_zeta___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_zeta___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_zeta___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_zeta___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_zeta___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
        14634483482441683967 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_DSimp_zeta___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__0_value) as *mut LeanObject,
        16596319664338446668 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_zeta___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_zeta___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_zeta___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_zeta___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_zeta___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_zeta: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zeta___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_zetaDelta___closed__0_value: LeanStringObject<10> =
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
        m_data: [122, 101, 116, 97, 68, 101, 108, 116, 97, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_zetaDelta___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
            14634483482441683967 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__0_value)
                as *mut LeanObject,
            2119463912076888173 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_zetaDelta___closed__2_value: LeanStringObject<11> =
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
        m_data: [122, 101, 116, 97, 95, 100, 101, 108, 116, 97, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_zetaDelta___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_zetaDelta___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_zetaDelta___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_zetaDelta___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_zetaDelta___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_zetaDelta: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_zetaDelta___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_proj___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [112, 114, 111, 106, 0],
};
static mut l_Lean_Parser_Sym_DSimp_proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_proj___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_proj___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_proj___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_proj___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
        14634483482441683967 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_DSimp_proj___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__0_value) as *mut LeanObject,
        15045140164005891883 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_proj___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_proj___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_proj___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_reduceMatch___closed__0_value: LeanStringObject<12> =
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
        m_data: [114, 101, 100, 117, 99, 101, 77, 97, 116, 99, 104, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_reduceMatch___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
            14634483482441683967 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__0_value)
                as *mut LeanObject,
            14884666146178512216 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_reduceMatch___closed__2_value: LeanStringObject<6> =
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
        m_data: [109, 97, 116, 99, 104, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_reduceMatch___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_reduceMatch___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_reduceMatch___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_reduceMatch___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_reduceMatch___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_reduceMatch: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_reduceMatch___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_andThen___closed__0_value: LeanStringObject<8> =
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
        m_data: [97, 110, 100, 84, 104, 101, 110, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_andThen___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_andThen___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_andThen___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_andThen___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_andThen___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
            14634483482441683967 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_DSimp_andThen___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__0_value) as *mut LeanObject,
        15118032029328637794 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_andThen___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_andThen___closed__2_value: LeanStringObject<5> =
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
        m_data: [32, 62, 62, 32, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_andThen___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_andThen___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_andThen___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_andThen___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__11_value)
            as *mut LeanObject,
        (((60 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_andThen___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_andThen___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_andThen___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_andThen___closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__1_value) as *mut LeanObject,
        (((60 as usize) << 1) | 1) as *mut LeanObject,
        (((61 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_andThen___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_andThen: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_andThen___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_orElse___closed__0_value: LeanStringObject<7> =
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
        m_data: [111, 114, 69, 108, 115, 101, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_orElse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_orElse___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_orElse___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_orElse___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_DSimp_orElse___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
        14634483482441683967 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_DSimp_orElse___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__0_value) as *mut LeanObject,
        12448059518168016466 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_orElse___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_orElse___closed__2_value: LeanStringObject<6> =
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
        m_data: [32, 60, 124, 62, 32, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_orElse___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_orElse___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_orElse___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_orElse___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__11_value)
            as *mut LeanObject,
        (((20 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_orElse___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_orElse___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_orElse___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_orElse___closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__1_value) as *mut LeanObject,
        (((20 as usize) << 1) | 1) as *mut LeanObject,
        (((21 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_DSimp_orElse___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_orElse: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_orElse___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__0_value: LeanStringObject<14> =
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
            100, 115, 105, 109, 112, 114, 111, 99, 80, 97, 114, 101, 110, 0,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_none___closed__1_value) as *mut LeanObject,
            14634483482441683967 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__0_value)
                as *mut LeanObject,
            12358822129129543384 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__2_value: LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_DSimp_dsimprocParen: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_dsimprocParen___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__0_value: LeanStringObject<16> =
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
            115, 121, 109, 95, 100, 115, 105, 109, 112, 95, 102, 105, 101, 108, 100, 0,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__0_value)
                as *mut LeanObject,
            6679455632227939271 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Parser_Command_sym__dsimp__field_quot___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__3_value)
                as *mut LeanObject,
            4493126045881830933 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__2_value: LeanStringObject<20> =
    LeanStringObject {
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
            96, 40, 115, 121, 109, 95, 100, 115, 105, 109, 112, 95, 102, 105, 101, 108, 100, 124,
            32, 0,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__0_value)
                as *mut LeanObject,
            6679455632227939271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__dsimp__field_quot___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__dsimp__field_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_sym__dsimp__field_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Category_sym__dsimp__field: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__0_value: LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__1_value: LeanStringObject<17> =
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
            115, 121, 109, 68, 83, 105, 109, 112, 70, 105, 101, 108, 100, 80, 114, 101, 0,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__1_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_symDSimpFieldPre___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symDSimpFieldPre___closed__2_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symDSimpFieldPre___closed__2_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__1_value)
                as *mut LeanObject,
            1566494510409085648 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__3_value: LeanStringObject<4> =
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
        m_data: [112, 114, 101, 0],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__4_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__3_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__5_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPre___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__2_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPre___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_symDSimpFieldPre: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPost___closed__0_value: LeanStringObject<18> =
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
            115, 121, 109, 68, 83, 105, 109, 112, 70, 105, 101, 108, 100, 80, 111, 115, 116, 0,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPost___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_symDSimpFieldPost___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symDSimpFieldPost___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symDSimpFieldPost___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_symDSimpFieldPost___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__0_value)
                as *mut LeanObject,
            7104639290947524305 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPost___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPost___closed__2_value: LeanStringObject<5> =
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
        m_data: [112, 111, 115, 116, 0],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPost___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPost___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPost___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPost___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPost___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPost___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPost___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldPost___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldPost___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_symDSimpFieldPost: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPost___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__0_value: LeanStringObject<22> =
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
            115, 121, 109, 68, 83, 105, 109, 112, 70, 105, 101, 108, 100, 77, 97, 120, 83, 116,
            101, 112, 115, 0,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__0_value)
                as *mut LeanObject,
            9043302130081388410 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__2_value: LeanStringObject<9> =
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
        m_data: [109, 97, 120, 83, 116, 101, 112, 115, 0],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__5_value: LeanStringObject<4> =
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
        m_data: [110, 117, 109, 0],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__5_value)
                as *mut LeanObject,
            6110315075117401315 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_symDSimpFieldMaxSteps: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldMaxSteps___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__0_value: LeanStringObject<17> =
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
            114, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 68, 83, 105, 109, 112, 0,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_registerSymDSimp___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSymDSimp___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSymDSimp___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symDSimpFieldPre___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_registerSymDSimp___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__0_value)
                as *mut LeanObject,
            11904518328331150023 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__2_value: LeanStringObject<19> =
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
            114, 101, 103, 105, 115, 116, 101, 114, 95, 115, 121, 109, 95, 100, 115, 105, 109, 112,
            0,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__4_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Command_registerSymDSimp___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__4_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__8_value: LeanStringObject<6> =
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
        m_data: [119, 104, 101, 114, 101, 0],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__11_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Command_registerSymDSimp___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__11_value)
                as *mut LeanObject,
            2302572775315350313 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__13_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Command_registerSymDSimp___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__13_value)
                as *mut LeanObject,
            17597206043415342265 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__15_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__dsimp__field_quot___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__17_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_DSimp_sym__dsimproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymDSimp___closed__19_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymDSimp___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__19_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_registerSymDSimp: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymDSimp___closed__19_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Lean_Parser_Category_sym__dsimproc() -> *mut LeanObject {
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    v___x_426_ = lean_box(0);
    return v___x_426_;
}
pub unsafe fn _init_l_Lean_Parser_Category_sym__dsimp__field() -> *mut LeanObject {
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    v___x_635_ = lean_box(0);
    return v___x_635_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Sym_DSimp_DSimprocDSL(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn meta_initialize_Init_Sym_DSimp_DSimprocDSL(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Category_sym__dsimproc = _init_l_Lean_Parser_Category_sym__dsimproc();
    lean_mark_persistent(l_Lean_Parser_Category_sym__dsimproc);
    l_Lean_Parser_Category_sym__dsimp__field = _init_l_Lean_Parser_Category_sym__dsimp__field();
    lean_mark_persistent(l_Lean_Parser_Category_sym__dsimp__field);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Sym_DSimp_DSimprocDSL(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
}
