// Lean compiler output
// Module: Lean.Elab.ConfigEval.Commands
// Imports: Init.Notation
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value: LeanStringObject<5> =
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
        m_data: [69, 108, 97, 98, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value: LeanStringObject<11> =
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
        m_data: [67, 111, 110, 102, 105, 103, 69, 118, 97, 108, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__3_value: LeanStringObject<23> =
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
            101, 110, 115, 117, 114, 101, 69, 118, 97, 108, 84, 101, 114, 109, 73, 110, 115, 116,
            97, 110, 99, 101, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__3_value)
                as *mut LeanObject,
            15782017376166539708 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__5_value: LeanStringObject<8> =
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
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__5_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__7_value: LeanStringObject<9> =
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
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__7_value)
                as *mut LeanObject,
            18170484695678750185 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__9_value: LeanStringObject<11> =
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
        m_data: [118, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__9_value)
                as *mut LeanObject,
            18370519569176055110 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__12_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__13_value: LeanStringObject<9> =
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
        m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__13_value)
                as *mut LeanObject,
            16084902538479694224 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__14_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__17_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            101, 110, 115, 117, 114, 101, 95, 101, 118, 97, 108, 95, 116, 101, 114, 109, 95, 105,
            110, 115, 116, 97, 110, 99, 101, 32, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__18_value: LeanCtorObject<1> =
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
            l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__17_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__19_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__20_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__21_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__20_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__22_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__21_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__23_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__19_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__24_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__4_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__24_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_ensureEvalTermInstance: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__0_value: LeanStringObject<23> =
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
            101, 110, 115, 117, 114, 101, 69, 118, 97, 108, 69, 120, 112, 114, 73, 110, 115, 116,
            97, 110, 99, 101, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__0_value)
                as *mut LeanObject,
            242734749837126826 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__2_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            101, 110, 115, 117, 114, 101, 95, 101, 118, 97, 108, 95, 101, 120, 112, 114, 95, 105,
            110, 115, 116, 97, 110, 99, 101, 32, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__3_value: LeanCtorObject<1> =
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
            l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_ensureEvalExprInstance: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalExprInstance___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__0_value: LeanStringObject<
    28,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        101, 110, 115, 117, 114, 101, 69, 118, 97, 108, 84, 101, 114, 109, 69, 120, 112, 114, 73,
        110, 115, 116, 97, 110, 99, 101, 115, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1_value_aux_1: LeanCtorObject<
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
            l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
            as *mut LeanObject,
        11364794674035624021 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__0_value
            ) as *mut LeanObject,
            13281077697210892810 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__2_value: LeanStringObject<
    33,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        101, 110, 115, 117, 114, 101, 95, 101, 118, 97, 108, 95, 116, 101, 114, 109, 95, 101, 120,
        112, 114, 95, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__3_value: LeanCtorObject<1> =
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
            l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__3_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__4_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__6_value: LeanCtorObject<3> =
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
                l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__1_value
            ) as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__5_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermExprInstances___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
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
            100, 101, 114, 105, 118, 101, 69, 118, 97, 108, 69, 120, 112, 114, 85, 115, 105, 110,
            103, 77, 101, 116, 97, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__0_value)
                as *mut LeanObject,
            5814452243651064866 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__2_value: LeanStringObject<43> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 43,
        m_capacity: 43,
        m_length: 42,
        m_data: [
            100, 101, 114, 105, 118, 101, 95, 101, 118, 97, 108, 95, 101, 120, 112, 114, 95, 105,
            110, 115, 116, 97, 110, 99, 101, 95, 117, 115, 105, 110, 103, 95, 109, 101, 116, 97,
            95, 101, 118, 97, 108, 32, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__3_value: LeanCtorObject<1> =
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
            l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_deriveEvalExprUsingMeta___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__0_value: LeanStringObject<16> =
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
            99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 79, 109, 105, 116, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__0_value)
                as *mut LeanObject,
            5452356098271972433 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__2_value: LeanStringObject<6> =
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
        m_data: [111, 109, 105, 116, 32, 0],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__4_value: LeanStringObject<6> =
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
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__4_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__7_value: LeanStringObject<2> =
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
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__8_value: LeanStringObject<3> =
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
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__10_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 11,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__9_value)
                as *mut LeanObject,
            1 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryOmit___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryOmit___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__12_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_configEntryOmit: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0_value: LeanStringObject<
    28,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 72, 97, 110, 100, 108, 101, 114, 75,
        101, 121, 80, 114, 101, 102, 105, 120, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_1: LeanCtorObject<
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
            l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_2: LeanCtorObject<
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
            l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
            as *mut LeanObject,
        11364794674035624021 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0_value
            ) as *mut LeanObject,
            5170656903224962469 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2_value: LeanStringObject<
    5,
> = LeanStringObject {
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
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
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
                l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__2_value
            ) as *mut LeanObject,
            1581446985683836252 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__3_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5_value: LeanStringObject<
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
    m_data: [46, 0],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6_value: LeanCtorObject<1> =
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
            l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__5_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__6_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__7_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__4_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9_value: LeanStringObject<
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
    m_data: [42, 0],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10_value: LeanCtorObject<
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
        l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__9_value
    ) as *mut LeanObject],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__11_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__12_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__1_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__13_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0_value:
    LeanStringObject<30> = LeanStringObject {
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
        99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 72, 97, 110, 100, 108, 101, 114, 75,
        101, 121, 87, 105, 108, 100, 99, 97, 114, 100, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_1:
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
            l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_2:
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
            l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
            as *mut LeanObject,
        11364794674035624021 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value: LeanCtorObject<
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
            l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0_value)
            as *mut LeanObject,
        6766706904888361041 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__1_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__10_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0_value: LeanStringObject<22> =
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
            99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 72, 97, 110, 100, 108, 101, 114,
            75, 101, 121, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0_value)
                as *mut LeanObject,
            15143275316288011801 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__2_value)
                as *mut LeanObject,
            393173242845875278 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_configEntryHandlerKeyPrefix___closed__14_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ConfigEval_configEntryHandlerKeyWildcard___closed__2_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_configEntryHandlerKey: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__0_value: LeanStringObject<19> =
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
            99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 72, 97, 110, 100, 108, 101, 114, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__0_value)
                as *mut LeanObject,
            3045336378954125646 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__2_value: LeanStringObject<8> =
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
        m_data: [111, 112, 116, 105, 111, 110, 32, 0],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__5_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntryHandler___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntryHandler___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_configEntryHandler: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntry___closed__0_value: LeanStringObject<12> =
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
        m_data: [99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 121, 0],
    };
static mut l_Lean_Elab_ConfigEval_configEntry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_configEntry___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__0_value)
                as *mut LeanObject,
            9645242084791194988 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntry___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntry___closed__2_value: LeanStringObject<8> =
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
static mut l_Lean_Elab_ConfigEval_configEntry___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntry___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__2_value)
                as *mut LeanObject,
            15964447885077099669 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntry___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntry___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandlerKey___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryHandler___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntry___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntry___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntry___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntry___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntry___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_configEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntries___closed__0_value: LeanStringObject<14> =
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
            99, 111, 110, 102, 105, 103, 69, 110, 116, 114, 105, 101, 115, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntries___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_configEntries___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__0_value)
                as *mut LeanObject,
            2209778251590303698 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntries___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntries___closed__2_value: LeanStringObject<7> =
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
        m_data: [32, 119, 104, 101, 114, 101, 0],
    };
static mut l_Lean_Elab_ConfigEval_configEntries___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntries___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntries___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntries___closed__4_value: LeanStringObject<21> =
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
static mut l_Lean_Elab_ConfigEval_configEntries___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntries___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__4_value)
                as *mut LeanObject,
            8450841259565682059 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntries___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntries___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntry___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntries___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntries___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntries___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_configEntries___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_configEntries___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_configEntries: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__0_value: LeanStringObject<21> =
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
            100, 101, 102, 69, 118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 67,
            109, 100, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__0_value)
                as *mut LeanObject,
            15774958811162948289 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__2_value: LeanStringObject<11> =
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
        m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__2_value)
                as *mut LeanObject,
            3961966953292576997 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__4_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__8_value: LeanStringObject<22> =
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
            100, 101, 102, 95, 101, 118, 97, 108, 95, 99, 111, 110, 102, 105, 103, 95, 105, 116,
            101, 109, 32, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__12_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__13_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__12_value)
                as *mut LeanObject,
            2302572775315350313 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__14_value: LeanStringObject<16> =
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
            98, 114, 97, 99, 107, 101, 116, 101, 100, 66, 105, 110, 100, 101, 114, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__14_value)
                as *mut LeanObject,
            2222647442666011774 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__16_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__19_value: LeanStringObject<6> =
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
        m_data: [32, 102, 111, 114, 32, 0],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__20_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__21_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__22_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__21_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntries___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__24_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__22_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__24_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_defEvalConfigItemCmd: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__0_value: LeanStringObject<22> =
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
            100, 101, 99, 108, 97, 114, 101, 67, 111, 114, 101, 67, 111, 110, 102, 105, 103, 69,
            108, 97, 98, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__0_value)
                as *mut LeanObject,
            10628568370346925746 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__2_value: LeanStringObject<25> =
    LeanStringObject {
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
            100, 101, 99, 108, 97, 114, 101, 95, 99, 111, 114, 101, 95, 99, 111, 110, 102, 105,
            103, 95, 101, 108, 97, 98, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_declareCoreConfigElab: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCoreConfigElab___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__0_value: LeanStringObject<22> =
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
            100, 101, 99, 108, 97, 114, 101, 84, 101, 114, 109, 67, 111, 110, 102, 105, 103, 69,
            108, 97, 98, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__0_value)
                as *mut LeanObject,
            8913075533519350929 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__2_value: LeanStringObject<25> =
    LeanStringObject {
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
            100, 101, 99, 108, 97, 114, 101, 95, 116, 101, 114, 109, 95, 99, 111, 110, 102, 105,
            103, 95, 101, 108, 97, 98, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_declareTermConfigElab: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTermConfigElab___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__0_value: LeanStringObject<20> =
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
            100, 101, 99, 108, 97, 114, 101, 84, 97, 99, 116, 105, 99, 67, 111, 110, 102, 105, 103,
            0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__0_value)
                as *mut LeanObject,
            14052075957971063135 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__2_value: LeanStringObject<20> =
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
            100, 101, 99, 108, 97, 114, 101, 95, 99, 111, 110, 102, 105, 103, 95, 101, 108, 97, 98,
            0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareTacticConfig___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareTacticConfig___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_declareTacticConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareTacticConfig___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__0_value: LeanStringObject<21> =
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
            100, 101, 99, 108, 97, 114, 101, 67, 111, 109, 109, 97, 110, 100, 67, 111, 110, 102,
            105, 103, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__1_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__2_value)
                as *mut LeanObject,
            11364794674035624021 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__0_value)
                as *mut LeanObject,
            7457840639043711308 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__2_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            100, 101, 99, 108, 97, 114, 101, 95, 99, 111, 109, 109, 97, 110, 100, 95, 99, 111, 110,
            102, 105, 103, 95, 101, 108, 97, 98, 0,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_configEntryOmit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_ensureEvalTermInstance___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_defEvalConfigItemCmd___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ConfigEval_declareCommandConfig___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ConfigEval_declareCommandConfig___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_ConfigEval_declareCommandConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_declareCommandConfig___closed__9_value)
        as *mut LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_Commands(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval_Commands(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_Commands(builtin);
}
