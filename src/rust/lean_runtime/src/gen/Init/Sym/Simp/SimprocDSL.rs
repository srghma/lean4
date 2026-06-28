// Lean compiler output
// Module: Init.Sym.Simp.SimprocDSL
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
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__2_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__3_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__3_value)
        as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__3_value)
                as *mut LeanObject,
            5855146430765573009 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__5_value: LeanStringObject<12> =
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
        m_data: [115, 121, 109, 95, 115, 105, 109, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__5_value)
        as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__6_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__5_value)
                as *mut LeanObject,
            17663670605732064950 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__3_value)
                as *mut LeanObject,
            4915525502455682736 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__7_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__7_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__9_value: LeanStringObject<16> =
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
            96, 40, 115, 121, 109, 95, 115, 105, 109, 112, 114, 111, 99, 124, 32, 0,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__10_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__5_value)
                as *mut LeanObject,
            17663670605732064950 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__12_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__11_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__13_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__14_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__6_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__18_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_sym__simproc_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__18_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Category_sym__simproc: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__0_value: LeanStringObject<15> =
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
            115, 121, 109, 95, 100, 105, 115, 99, 104, 97, 114, 103, 101, 114, 0,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__0_value)
                as *mut LeanObject,
            16913365718413729959 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__3_value)
                as *mut LeanObject,
            7999847994946158837 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__2_value: LeanStringObject<19> =
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
            96, 40, 115, 121, 109, 95, 100, 105, 115, 99, 104, 97, 114, 103, 101, 114, 124, 32, 0,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__0_value)
                as *mut LeanObject,
            16913365718413729959 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_sym__discharger_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Category_sym__discharger: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Sym_Simp_ground___closed__0_value: LeanStringObject<4> =
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
        m_data: [83, 121, 109, 0],
    };
static mut l_Lean_Parser_Sym_Simp_ground___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_ground___closed__1_value: LeanStringObject<5> =
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
        m_data: [83, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Sym_Simp_ground___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_ground___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_Parser_Sym_Simp_ground___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_ground___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_ground___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_ground___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_ground___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__3_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
        17762876748869580590 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_Simp_ground___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__3_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__2_value) as *mut LeanObject,
        15642365844547147657 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_ground___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_ground___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_ground___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_ground___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__3_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_ground___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_ground: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_telescope___closed__0_value: LeanStringObject<10> =
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
        m_data: [116, 101, 108, 101, 115, 99, 111, 112, 101, 0],
    };
static mut l_Lean_Parser_Sym_Simp_telescope___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_telescope___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_telescope___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_telescope___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_telescope___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
            17762876748869580590 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_telescope___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__0_value) as *mut LeanObject,
        4998230570037354350 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_telescope___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_telescope___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_telescope___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_telescope___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_telescope___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_telescope: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_telescope___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_control___closed__0_value: LeanStringObject<8> =
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
        m_data: [99, 111, 110, 116, 114, 111, 108, 0],
    };
static mut l_Lean_Parser_Sym_Simp_control___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_control___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_control___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_control___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_control___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
        17762876748869580590 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_Simp_control___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__0_value) as *mut LeanObject,
        5081612414781455787 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_control___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_control___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_control___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_control___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_control___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_control: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_control___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_arrowTelescope___closed__0_value: LeanStringObject<15> =
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
            97, 114, 114, 111, 119, 84, 101, 108, 101, 115, 99, 111, 112, 101, 0,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_arrowTelescope___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
            17762876748869580590 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__0_value)
                as *mut LeanObject,
            7377854587226246167 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_arrowTelescope___closed__2_value: LeanStringObject<16> =
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
            97, 114, 114, 111, 119, 95, 116, 101, 108, 101, 115, 99, 111, 112, 101, 0,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_arrowTelescope___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_arrowTelescope___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_arrowTelescope___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_arrowTelescope___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_arrowTelescope___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_arrowTelescope: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_arrowTelescope___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__0_value: LeanStringObject<11> =
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
        m_data: [114, 101, 119, 114, 105, 116, 101, 83, 101, 116, 0],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
            17762876748869580590 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__0_value)
                as *mut LeanObject,
            10120069549607349517 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__2_value: LeanStringObject<8> =
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
        m_data: [114, 101, 119, 114, 105, 116, 101, 0],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__4_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__4_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__8_value: LeanStringObject<9> =
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
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__8_value)
                as *mut LeanObject,
            18170484695678750185 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__10_value: LeanStringObject<7> =
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
        m_data: [32, 119, 105, 116, 104, 32, 0],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__13_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteSet___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteSet___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__15_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_rewriteSet: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__0_value: LeanStringObject<14> =
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
            114, 101, 119, 114, 105, 116, 101, 73, 110, 108, 105, 110, 101, 0,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
            17762876748869580590 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__0_value)
                as *mut LeanObject,
            5467082909805454615 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__2_value: LeanStringObject<3> =
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
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__5_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__6_value: LeanStringObject<3> =
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
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__8_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__7_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__10_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_rewriteInline___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_rewriteInline___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__14_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_rewriteInline: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteInline___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_self___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 101, 108, 102, 0],
};
static mut l_Lean_Parser_Sym_Simp_self___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_self___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_self___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_self___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_self___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
        17762876748869580590 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_Simp_self___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__1_value_aux_3) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__0_value) as *mut LeanObject,
        3624192759600632721 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_self___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_self___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_self___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_self___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_self___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_self: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_none___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Parser_Sym_Simp_none___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_none___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_none___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_none___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_none___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
        17762876748869580590 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_Simp_none___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__1_value_aux_3) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__0_value) as *mut LeanObject,
        5819120222105569584 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_none___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_none___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_none___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_none___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_none___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_none: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_andThen___closed__0_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Sym_Simp_andThen___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_andThen___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_andThen___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_andThen___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_andThen___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
        17762876748869580590 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_Simp_andThen___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__0_value) as *mut LeanObject,
        564218847374344423 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_andThen___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_andThen___closed__2_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Sym_Simp_andThen___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_andThen___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_andThen___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_andThen___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__11_value)
            as *mut LeanObject,
        (((60 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_andThen___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_andThen___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_andThen___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_andThen___closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__1_value) as *mut LeanObject,
        (((60 as usize) << 1) | 1) as *mut LeanObject,
        (((61 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_andThen___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_andThen: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_andThen___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_orElse___closed__0_value: LeanStringObject<7> =
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
static mut l_Lean_Parser_Sym_Simp_orElse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_orElse___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_orElse___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_orElse___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
        17473872748478919658 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Sym_Simp_orElse___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
        17762876748869580590 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Sym_Simp_orElse___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__0_value) as *mut LeanObject,
        11113107058493755383 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_orElse___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_orElse___closed__2_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Sym_Simp_orElse___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_orElse___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_orElse___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_orElse___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__11_value)
            as *mut LeanObject,
        (((20 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_orElse___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_orElse___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_orElse___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_orElse___closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__1_value) as *mut LeanObject,
        (((20 as usize) << 1) | 1) as *mut LeanObject,
        (((21 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_orElse___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_orElse: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_orElse___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_simprocParen___closed__0_value: LeanStringObject<13> =
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
        m_data: [115, 105, 109, 112, 114, 111, 99, 80, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Parser_Sym_Simp_simprocParen___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
            17762876748869580590 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__0_value)
                as *mut LeanObject,
            15836888127685990580 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_simprocParen___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_simprocParen___closed__2_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_Sym_Simp_simprocParen___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_simprocParen___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_simprocParen___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_simprocParen___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_simprocParen___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_simprocParen___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_simprocParen___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_simprocParen___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_simprocParen___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_simprocParen: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_dischSelf___closed__0_value: LeanStringObject<10> =
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
        m_data: [100, 105, 115, 99, 104, 83, 101, 108, 102, 0],
    };
static mut l_Lean_Parser_Sym_Simp_dischSelf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
            17762876748869580590 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__0_value) as *mut LeanObject,
        16169981844629337600 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_dischSelf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_dischSelf___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_self___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_dischSelf___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_dischSelf: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischSelf___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_dischNone___closed__0_value: LeanStringObject<10> =
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
        m_data: [100, 105, 115, 99, 104, 78, 111, 110, 101, 0],
    };
static mut l_Lean_Parser_Sym_Simp_dischNone___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_dischNone___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_dischNone___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_dischNone___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_dischNone___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
            17762876748869580590 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_dischNone___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__0_value) as *mut LeanObject,
        12137791703934599550 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_dischNone___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_dischNone___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_none___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Sym_Simp_dischNone___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_dischNone: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischNone___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_dischParen___closed__0_value: LeanStringObject<11> =
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
        m_data: [100, 105, 115, 99, 104, 80, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Parser_Sym_Simp_dischParen___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Sym_Simp_dischParen___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_dischParen___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_dischParen___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__0_value) as *mut LeanObject,
            17473872748478919658 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Sym_Simp_dischParen___closed__1_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_ground___closed__1_value) as *mut LeanObject,
            17762876748869580590 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Sym_Simp_dischParen___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__0_value)
                as *mut LeanObject,
            381305762770861206 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_dischParen___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_dischParen___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_simprocParen___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__discharger_quot___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_dischParen___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_dischParen___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_dischParen___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Sym_Simp_dischParen___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Sym_Simp_dischParen___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Sym_Simp_dischParen: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_dischParen___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__0_value: LeanStringObject<15> =
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
            115, 121, 109, 95, 115, 105, 109, 112, 95, 102, 105, 101, 108, 100, 0,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_sym__simp__field_quot___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__0_value)
                as *mut LeanObject,
            12670494459664558895 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__3_value)
                as *mut LeanObject,
            1196906581075312669 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__2_value: LeanStringObject<19> =
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
            96, 40, 115, 121, 109, 95, 115, 105, 109, 112, 95, 102, 105, 101, 108, 100, 124, 32, 0,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__0_value)
                as *mut LeanObject,
            12670494459664558895 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_sym__simp__field_quot___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_sym__simp__field_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_sym__simp__field_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Category_sym__simp__field: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__0_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__1_value: LeanStringObject<16> =
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
            115, 121, 109, 83, 105, 109, 112, 70, 105, 101, 108, 100, 80, 114, 101, 0,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__1_value) as *mut LeanObject;
static l_Lean_Parser_Command_symSimpFieldPre___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symSimpFieldPre___closed__2_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symSimpFieldPre___closed__2_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__1_value)
                as *mut LeanObject,
            9189406429225494327 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__3_value: LeanStringObject<4> =
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
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__4_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__3_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__5_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPre___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__2_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPre___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Command_symSimpFieldPre: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPost___closed__0_value: LeanStringObject<17> =
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
            115, 121, 109, 83, 105, 109, 112, 70, 105, 101, 108, 100, 80, 111, 115, 116, 0,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPost___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_symSimpFieldPost___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symSimpFieldPost___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symSimpFieldPost___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_symSimpFieldPost___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__0_value)
                as *mut LeanObject,
            16195861106700361357 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPost___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPost___closed__2_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Command_symSimpFieldPost___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPost___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPost___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPost___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPost___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPost___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPost___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldPost___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldPost___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_symSimpFieldPost: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPost___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__0_value: LeanStringObject<21> =
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
            115, 121, 109, 83, 105, 109, 112, 70, 105, 101, 108, 100, 77, 97, 120, 83, 116, 101,
            112, 115, 0,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__0_value)
                as *mut LeanObject,
            1958772177027152643 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__2_value: LeanStringObject<9> =
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
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__5_value: LeanStringObject<4> =
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
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__5_value)
                as *mut LeanObject,
            6110315075117401315 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_symSimpFieldMaxSteps: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__0_value: LeanStringObject<
    30,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        115, 121, 109, 83, 105, 109, 112, 70, 105, 101, 108, 100, 77, 97, 120, 68, 105, 115, 99,
        104, 97, 114, 103, 101, 68, 101, 112, 116, 104, 0,
    ],
};
static mut l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1_value_aux_1: LeanCtorObject<
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
            l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1_value_aux_2: LeanCtorObject<
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
            l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1_value: LeanCtorObject<
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
            l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__0_value)
            as *mut LeanObject,
        6372041257667356148 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__2_value: LeanStringObject<
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
        109, 97, 120, 68, 105, 115, 99, 104, 97, 114, 103, 101, 68, 101, 112, 116, 104, 0,
    ],
};
static mut l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__3_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__2_value)
            as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__4_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__6_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__5_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxSteps___closed__7_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__6_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__1_value)
            as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldMaxDischargeDepth___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__0_value: LeanStringObject<16> =
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
            114, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 83, 105, 109, 112, 0,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Command_registerSymSimp___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSymSimp___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSymSimp___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_symSimpFieldPre___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_registerSymSimp___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__0_value)
                as *mut LeanObject,
            258076495819451832 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__2_value: LeanStringObject<18> =
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
            114, 101, 103, 105, 115, 116, 101, 114, 95, 115, 121, 109, 95, 115, 105, 109, 112, 0,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_rewriteSet___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__5_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Command_registerSymSimp___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__8_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Command_registerSymSimp___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__8_value)
                as *mut LeanObject,
            2302572775315350313 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__10_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Command_registerSymSimp___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__10_value)
                as *mut LeanObject,
            17597206043415342265 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__12_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_sym__simp__field_quot___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__14_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Sym_Simp_sym__simproc_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSymSimp___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSymSimp___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__16_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_registerSymSimp: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimp___closed__16_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Lean_Parser_Category_sym__simproc() -> *mut LeanObject {
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    v___x_587_ = lean_box(0);
    return v___x_587_;
}
pub unsafe fn _init_l_Lean_Parser_Category_sym__discharger() -> *mut LeanObject {
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    v___x_617_ = lean_box(0);
    return v___x_617_;
}
pub unsafe fn _init_l_Lean_Parser_Category_sym__simp__field() -> *mut LeanObject {
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    v___x_939_ = lean_box(0);
    return v___x_939_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Sym_Simp_SimprocDSL(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn meta_initialize_Init_Sym_Simp_SimprocDSL(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Category_sym__simproc = _init_l_Lean_Parser_Category_sym__simproc();
    lean_mark_persistent(l_Lean_Parser_Category_sym__simproc);
    l_Lean_Parser_Category_sym__discharger = _init_l_Lean_Parser_Category_sym__discharger();
    lean_mark_persistent(l_Lean_Parser_Category_sym__discharger);
    l_Lean_Parser_Category_sym__simp__field = _init_l_Lean_Parser_Category_sym__simp__field();
    lean_mark_persistent(l_Lean_Parser_Category_sym__simp__field);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Sym_Simp_SimprocDSL(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Sym_Simp_SimprocDSL(builtin);
}
