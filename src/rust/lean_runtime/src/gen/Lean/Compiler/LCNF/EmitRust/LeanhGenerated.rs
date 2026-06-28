// Lean compiler output
// Module: Lean.Compiler.LCNF.EmitRust.LeanhGenerated
// Imports: Init Init Init.Prelude
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
use crate::r#gen::Init::{initialize_Init, meta_initialize_Init, runtime_initialize_Init};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__0_value: LeanStringObject<4> =
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
        m_data: [116, 97, 110, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__1_value: LeanStringObject<5> =
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
        m_data: [116, 97, 110, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__2_value: LeanStringObject<5> =
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
        m_data: [116, 97, 110, 104, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__3_value: LeanStringObject<6> =
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
        m_data: [116, 97, 110, 104, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__4_value: LeanStringObject<5> =
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
        m_data: [115, 105, 110, 104, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__5_value: LeanStringObject<6> =
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
        m_data: [115, 105, 110, 104, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__6_value: LeanStringObject<5> =
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
        m_data: [115, 113, 114, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__7_value: LeanStringObject<6> =
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
        m_data: [115, 113, 114, 116, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__8_value: LeanStringObject<5> =
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
        m_data: [108, 111, 103, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__9_value: LeanStringObject<4> =
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
        m_data: [112, 111, 119, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__10_value: LeanStringObject<5> =
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
        m_data: [112, 111, 119, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__11_value: LeanStringObject<6> =
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
        m_data: [114, 111, 117, 110, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__12_value: LeanStringObject<7> =
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
        m_data: [114, 111, 117, 110, 100, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__13_value: LeanStringObject<4> =
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
        m_data: [115, 105, 110, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__14_value: LeanStringObject<5> =
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
        m_data: [115, 105, 110, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__15_value: LeanStringObject<15> =
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
            108, 108, 118, 109, 95, 103, 101, 116, 95, 112, 97, 114, 97, 109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__16_value: LeanStringObject<20> =
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
            108, 108, 118, 109, 95, 105, 115, 95, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
            110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__17_value: LeanStringObject<4> =
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
        m_data: [108, 111, 103, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__18_value: LeanStringObject<6> =
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
        m_data: [108, 111, 103, 49, 48, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__19_value: LeanStringObject<7> =
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
        m_data: [108, 111, 103, 49, 48, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__20_value: LeanStringObject<5> =
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
        m_data: [108, 111, 103, 50, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__21_value: LeanStringObject<6> =
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
        m_data: [108, 111, 103, 50, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__22_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 109,
            105, 110, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__23_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 112,
            97, 116, 99, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__24_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 115,
            112, 101, 99, 105, 97, 108, 95, 100, 101, 115, 99, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__25_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 118, 111, 105, 100, 95, 109, 107, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26_value: LeanStringObject<10> =
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
        m_data: [108, 101, 97, 110, 95, 119, 104, 110, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__27_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 119, 105, 110, 100, 111, 119, 115, 95, 103, 101, 116, 95, 110,
            101, 120, 116, 95, 116, 114, 97, 110, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__28_value: LeanStringObject<18> =
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
            108, 108, 118, 109, 95, 99, 111, 117, 110, 116, 95, 112, 97, 114, 97, 109, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__29_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 109, 117,
            108, 116, 105, 99, 97, 115, 116, 95, 108, 111, 111, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__30_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 109, 117,
            108, 116, 105, 99, 97, 115, 116, 95, 116, 116, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__30_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__31_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 116, 116,
            108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__32_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 119, 97, 105, 116, 95, 114,
            101, 97, 100, 97, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__32_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__33_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 112, 116, 105, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__34_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 105,
            115, 95, 114, 101, 108, 101, 97, 115, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__34_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__35_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 109,
            97, 106, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__35_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__36_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 103, 101, 116, 115, 111, 99,
            107, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__37_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 110, 101, 119, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__37_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__38_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 114, 101, 99, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__39_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__39_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__40_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 98, 114,
            111, 97, 100, 99, 97, 115, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__40_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__41_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 109, 101,
            109, 98, 101, 114, 115, 104, 105, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__41_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__42_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 109, 117,
            108, 116, 105, 99, 97, 115, 116, 95, 105, 110, 116, 101, 114, 102, 97, 99, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__42_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__43_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 105, 109, 101, 114, 95, 110, 101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__43_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__44_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 105, 109, 101, 114, 95, 114, 101, 115, 101,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__44_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__45_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 105, 109, 101, 114, 95, 115, 116, 111, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__45_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__46_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 98, 105, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__46_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__47_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 99, 97, 110, 99, 101, 108, 95,
            114, 101, 99, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__47_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__48_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 99, 111, 110, 110, 101, 99,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__48_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__49_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 103, 101, 116, 112, 101, 101,
            114, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__49_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__50_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 114, 101, 99, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__50_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__51_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 115, 101, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__51_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__52_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 115, 104, 117, 116, 100, 111,
            119, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__52_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__53_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 116, 114, 121, 95, 97, 99, 99,
            101, 112, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__53_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__54_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 119, 97, 105, 116, 95, 114, 101,
            97, 100, 97, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__54_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__55_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 105, 109, 101, 114, 95, 99, 97, 110, 99, 101,
            108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__55_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__56_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 105, 109, 101, 114, 95, 109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__56_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__57_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 107, 101, 101, 112, 97, 108,
            105, 118, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__57_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__58_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 108, 105, 115, 116, 101, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__58_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__59_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 110, 101, 119, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__59_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__60_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 110, 111, 100, 101, 108, 97,
            121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__60_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__61_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 99, 97, 110, 99, 101, 108, 95,
            114, 101, 99, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__61_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__62_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 99, 111, 110, 110, 101, 99, 116,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__62_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__63_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 103, 101, 116, 112, 101, 101,
            114, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__63_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__64_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 103, 101, 116, 115, 111, 99,
            107, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__64_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__65_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 115, 105, 103, 110, 97, 108, 95, 99, 97, 110, 99,
            101, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__65: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__65_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__66_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 115, 105, 103, 110, 97, 108, 95, 109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__66: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__66_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__67_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 115, 105, 103, 110, 97, 108, 95, 110, 101, 120,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__67: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__67_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__68_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 115, 105, 103, 110, 97, 108, 95, 115, 116, 111,
            112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__68: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__68_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__69_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 97, 99, 99, 101, 112, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__69: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__69_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__70_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 98, 105, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__70: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__70_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__71_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 99, 97, 110, 99, 101, 108, 95,
            97, 99, 99, 101, 112, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__71: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__71_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__72_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 116, 109, 112, 100, 105, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__72: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__72_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__73_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 117, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__73: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__73_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__74_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 117, 110, 115, 101, 116, 101, 110,
            118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__74: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__74_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__75_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 112, 116, 111, 110, 95, 118, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__75: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__75_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__76_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 112, 116, 111, 110, 95, 118, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__76: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__76_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__77_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 114, 97, 110, 100, 111, 109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__77: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__77_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__78_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 117, 118, 95, 115, 101, 116, 95, 112, 114, 111, 99, 101, 115,
            115, 95, 116, 105, 116, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__78: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__78_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__79_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 104, 111, 115, 116,
            110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__79: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__79_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__80_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 112, 105, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__80: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__80_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__81_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 112, 112, 105, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__81: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__81_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__82_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 112, 114, 105, 111,
            114, 105, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__82: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__82_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__83_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 104, 111, 109, 101, 100, 105, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__83: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__83_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__84_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 115, 101, 116, 101, 110, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__84: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__84_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__85_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 115, 101, 116, 112, 114, 105, 111,
            114, 105, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__85: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__85_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__86_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 105, 110, 116, 101, 114, 102, 97, 99, 101, 95, 97,
            100, 100, 114, 101, 115, 115, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__86: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__86_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__87_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 110, 116, 111, 112, 95, 118, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__87: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__87_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__88_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 110, 116, 111, 112, 95, 118, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__88: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__88_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__89_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 101, 110, 118, 105, 114, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__89: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__89_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__90_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 95, 103, 114, 111,
            117, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__90: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__90_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__91_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 95, 112, 97, 115,
            115, 119, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__91: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__91_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__92_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 101, 110, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__92: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__92_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__93_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 97, 118, 97, 105, 108, 97, 98,
            108, 101, 95, 109, 101, 109, 111, 114, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__93: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__93_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__94_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 99, 111, 110, 115, 116, 114,
            97, 105, 110, 101, 100, 95, 109, 101, 109, 111, 114, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__94: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__94_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__95_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 102, 114, 101, 101, 95, 109,
            101, 109, 111, 114, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__95: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__95_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__96_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 112, 114, 111, 99, 101, 115,
            115, 95, 116, 105, 116, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__96: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__96_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__97_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 116, 111, 116, 97, 108, 95,
            109, 101, 109, 111, 114, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__97: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__97_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__98_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 114, 117, 115, 97, 103, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__98: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__98_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__99_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 104, 114, 116, 105, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__99: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__99_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__100_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 99, 112, 117, 95, 105, 110, 102, 111, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__100: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__100_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__101_value: LeanStringObject<12> =
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
        m_data: [108, 101, 97, 110, 95, 117, 118, 95, 99, 119, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__101: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__101_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__102_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 100, 110, 115, 95, 103, 101, 116, 95, 105, 110,
            102, 111, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__102: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__102_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__103_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 100, 110, 115, 95, 103, 101, 116, 95, 110, 97,
            109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__103: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__103_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__104_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 101, 118, 101, 110, 116, 95, 108, 111, 111, 112,
            95, 97, 108, 105, 118, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__104: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__104_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__105_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 101, 118, 101, 110, 116, 95, 108, 111, 111, 112,
            95, 99, 111, 110, 102, 105, 103, 117, 114, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__105: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__105_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__106_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 101, 120, 101, 112, 97, 116, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__106: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__106_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__107_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__107: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__107_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__108_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 117, 105, 110, 116,
            49, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__108: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__108_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__109_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 117, 105, 110, 116,
            51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__109: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__109_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__110_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 117, 105, 110, 116,
            54, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__110: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__110_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__111_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 117, 105, 110, 116,
            56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__111: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__111_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__112_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__112: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__112_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__113_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 117, 118, 95, 99, 104, 100, 105, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__113: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__113_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__114_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 115, 104, 105, 102, 116, 95, 114,
            105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__114: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__114_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__115_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__115: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__115_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__116_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__116: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__116_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__117_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__117: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__117_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__118_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__118: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__118_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__119_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__119: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__119_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__120_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 111, 102, 95, 110, 97, 116, 95,
            109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__120: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__120_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__121_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 115, 104, 105, 102, 116, 95, 108,
            101, 102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__121: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__121_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__122_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__122: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__122_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__123_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__123: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__123_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__124_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__124: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__124_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__125_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 108, 111, 103, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__125: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__125_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__126_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__126: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__126_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__127_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__127: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__127_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__128_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__128: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__128_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__129_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 117, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__129: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__129_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__130_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__130: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__130_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 117, 112, 100, 97, 116, 101, 95, 101, 110, 118, 95, 97, 116,
            116, 114, 105, 98, 117, 116, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__132_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__132: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__132_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__133_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 99, 111, 109, 112, 108, 101, 109,
            101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__133: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__133_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__134_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__134: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__134_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__135_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__135: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__135_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__136_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__136: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__136_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__137_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__137: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__137_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__138_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__138: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__138_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__139_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__139: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__139_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__140_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 117, 105, 110, 116,
            49, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__140: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__140_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__141_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 117, 105, 110, 116,
            51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__141: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__141_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__142_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 117, 105, 110, 116,
            54, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__142: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__142_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__143_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__143: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__143_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__144_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__144: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__144_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__145_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__145: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__145_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__146_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__146: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__146_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__147_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 111, 102, 95, 110, 97, 116, 95, 109,
            107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__147: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__147_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__148_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 115, 104, 105, 102, 116, 95, 108,
            101, 102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__148: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__148_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__149_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 115, 104, 105, 102, 116, 95, 114,
            105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__149: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__149_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__150_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__150: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__150_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__151_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__151: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__151_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__152_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__152: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__152_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__153_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__153: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__153_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__154_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__154: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__154_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__155_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 108, 111, 103, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__155: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__155_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__156_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__156: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__156_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__157_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 117, 105, 110,
            116, 49, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__157: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__157_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__158_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 117, 105, 110,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__158: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__158_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__159_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 117, 105, 110,
            116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__159: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__159_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__160_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 117, 115, 105,
            122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__160: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__160_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__161_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__161: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__161_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__162_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__162: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__162_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__163_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 99, 111, 109, 112, 108, 101, 109,
            101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__163: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__163_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__164_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 111, 102, 95, 110, 97, 116, 95,
            109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__164: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__164_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__165_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 115, 104, 105, 102, 116, 95,
            108, 101, 102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__165: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__165_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__166_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 115, 104, 105, 102, 116, 95,
            114, 105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__166: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__166_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__167_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__167: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__167_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__168_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__168: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__168_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__169_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__169: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__169_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__170_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__170: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__170_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__171_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__171: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__171_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__172_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__172: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__172_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__173_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__173: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__173_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__174_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__174: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__174_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__175_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__175: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__175_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__176_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 108, 111, 103, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__176: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__176_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__177_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__177: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__177_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__178_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 109, 105, 120, 95, 104, 97, 115,
            104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__178: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__178_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__179_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__179: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__179_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__180_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__180: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__180_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__181_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 99, 111, 109, 112, 108, 101,
            109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__181: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__181_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__182_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__182: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__182_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__183_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__183: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__183_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__184_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__184: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__184_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__185_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__185: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__185_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__186_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__186: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__186_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__187_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__187: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__187_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__188_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__188: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__188_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__189_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110,
            116, 49, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__189: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__189_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__190_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110,
            116, 54, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__190: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__190_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__191_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110,
            116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__191: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__191_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__192_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 117, 115, 105,
            122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__192: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__192_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__193_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__193: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__193_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__194_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__194: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__194_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__195_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__195: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__195_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__196_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 111, 102, 95, 110, 97, 116, 95,
            109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__196: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__196_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__197_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 115, 104, 105, 102, 116, 95,
            108, 101, 102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__197: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__197_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__198_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 115, 104, 105, 102, 116, 95,
            114, 105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__198: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__198_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__199_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__199: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__199_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__200_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__200: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__200_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__201_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__201: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__201_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__202_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__202: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__202_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__203_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__203: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__203_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__204_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 108, 111, 103, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__204: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__204_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__205_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__205: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__205_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__206_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__206: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__206_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__207_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 117, 105, 110,
            116, 54, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__207: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__207_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__208_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 117, 105, 110,
            116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__208: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__208_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__209_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 117, 115, 105,
            122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__209: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__209_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__210_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__210: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__210_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__211_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__211: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__211_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__212_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 99, 111, 109, 112, 108, 101,
            109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__212: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__212_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__213_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__213: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__213_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__214_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 115, 104, 105, 102, 116, 95,
            108, 101, 102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__214: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__214_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__215_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 115, 104, 105, 102, 116, 95,
            114, 105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__215: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__215_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__216_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__216: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__216_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__217_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__217: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__217_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__218_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__218: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__218_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__219_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__219: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__219_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__220_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 117, 105, 110,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__220: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__220_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__221_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 108, 111, 103, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__221: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__221_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__222_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__222: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__222_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__223_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__223: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__223_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__224_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__224: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__224_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__225_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__225: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__225_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__226_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__226: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__226_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__227_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 111, 102, 95, 110, 97, 116, 95,
            109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__227: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__227_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__228_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__228: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__228_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__229_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__229: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__229_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__230_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__230: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__230_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__231_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__231: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__231_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__232_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 116, 104, 117, 110, 107, 95, 112, 117, 114, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__232: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__232_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__233_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__233: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__233_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__234_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 99, 111, 109, 112, 108, 101,
            109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__234: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__234_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__235_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__235: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__235_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__236_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111,
            114, 109, 95, 119, 105, 110, 100, 111, 119, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__236: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__236_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__237_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 116, 97, 115, 107, 95, 98, 105, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__237: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__237_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__238_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 116, 97, 115, 107, 95, 103, 101, 116, 95, 111, 119, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__238: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__238_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__239_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 116, 97, 115, 107, 95, 109, 97, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__239: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__239_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__240_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 116, 97, 115, 107, 95, 112, 117, 114, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__240: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__240_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__241_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 116, 97, 115, 107, 95, 115, 112, 97, 119, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__241: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__241_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__242_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 116, 104, 117, 110, 107, 95, 103, 101, 116, 95, 111, 119, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__242: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__242_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 115, 121, 109, 95, 100, 115, 105, 109, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 115, 121, 109, 95, 115, 105, 109, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 121, 110, 116, 104, 95, 112, 101, 110, 100, 105, 110, 103,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__246_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111,
            114, 109, 95, 101, 109, 115, 99, 114, 105, 112, 116, 101, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__246: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__246_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__247_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111,
            114, 109, 95, 110, 98, 105, 116, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__247: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__247_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__248_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111,
            114, 109, 95, 111, 115, 120, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__248: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__248_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__249_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111,
            114, 109, 95, 116, 97, 114, 103, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__249: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__249_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 102, 114, 111,
            110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 103, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 105, 115, 101,
            109, 112, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 112, 114, 101,
            118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 116, 97, 107,
            101, 119, 104, 105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 116, 111, 115,
            116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 115, 121, 109, 95, 100, 101, 102, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__257_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 112,
            114, 101, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__257: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__257_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__258_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 115,
            101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__258: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__258_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__259_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 118, 97, 108, 105, 100, 97,
            116, 101, 95, 117, 116, 102, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__259: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__259_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 97, 108, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 98, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 100, 114, 111,
            112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 101, 120, 116,
            114, 97, 99, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__264_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 101,
            120, 116, 114, 97, 99, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__264: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__264_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__265_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 103,
            101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__265: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__265_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__266_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 103,
            101, 116, 95, 98, 97, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__266: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__266_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__267_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 103,
            101, 116, 95, 102, 97, 115, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__267: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__267_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__268_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 103,
            101, 116, 95, 111, 112, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__268: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__268_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__269_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 110,
            101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__269: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__269_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__270_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 110,
            101, 120, 116, 95, 102, 97, 115, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__270: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__270_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 112, 111, 115, 111, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__272_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 112, 117, 115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__272: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__272_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 112, 117, 115, 104, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__274_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 116, 111, 95, 117, 116, 102,
            56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__274: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__274_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 116, 114, 105, 109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__276_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 97,
            116, 95, 101, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__276: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__276_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__277_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 98,
            121, 116, 101, 95, 115, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__277: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__277_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__278_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 109, 101, 109, 99, 109, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__278: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__278_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__279_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__279: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__279_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 110, 101, 120, 116, 119, 104,
            105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__281_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 111, 102, 95, 117, 115, 105,
            122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__281: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__281_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 111, 102, 102, 115, 101, 116,
            111, 102, 112, 111, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 112, 111, 115, 95, 109, 105,
            110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 112, 111, 115, 95, 115, 117,
            98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__285_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 105, 115, 95, 118, 97, 108,
            105, 100, 95, 112, 111, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__285: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__285_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 105, 115, 101, 109, 112, 116,
            121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 105, 115, 112, 114, 101, 102,
            105, 120, 111, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__288_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 108, 101, 110, 103, 116, 104,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__288: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__288_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 102, 114, 111, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__290_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 103, 101, 116, 95, 98, 121,
            116, 101, 95, 102, 97, 115, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__290: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__290_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__291_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 104, 97, 115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__291: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__291_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 105, 110, 116, 101, 114, 99,
            97, 108, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__293_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 100, 97, 116, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__293: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__293_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__294_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__294: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__294_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__295_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__295: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__295_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 100, 114, 111, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 100, 114, 111, 112, 114, 105,
            103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 102, 111, 108, 100, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__299_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 102, 114, 111, 109, 95, 117,
            116, 102, 56, 95, 117, 110, 99, 104, 101, 99, 107, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__299: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__299_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__300_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 99, 116, 95, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__300: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__300_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__301_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 99, 116, 95, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__301: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__301_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 97, 110, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__303_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 97, 112, 112, 101, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__303: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__303_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 99, 97, 112, 105, 116, 97,
            108, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__305_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 99, 111, 109, 112, 97, 114,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__305: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__305_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 99, 111, 110, 116, 97, 105,
            110, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__307_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 115, 116, 95, 109, 107, 95, 114, 101, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__307: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__307_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__308_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 115, 116, 95, 114, 101, 102, 95, 103, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__308: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__308_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__309_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 116, 95, 114, 101, 102, 95, 112, 116, 114, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__309: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__309_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__310_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 115, 116, 95, 114, 101, 102, 95, 115, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__310: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__310_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__311_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 115, 116, 95, 114, 101, 102, 95, 115, 119, 97, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__311: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__311_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__312_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 115, 116, 95, 114, 101, 102, 95, 116, 97, 107, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__312: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__312_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__313_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 115, 116, 97, 116, 101, 95, 115, 104, 97, 114, 101, 99, 111,
            109, 109, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__313: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__313_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__314_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 115, 104, 97, 114, 101, 99, 111, 109, 109, 111, 110, 95, 101,
            113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__314: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__314_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__315_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 115, 104, 97, 114, 101, 99, 111, 109, 109, 111, 110, 95, 104,
            97, 115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__315: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__315_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__316_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 115, 104, 97, 114, 101, 99, 111, 109, 109, 111, 110, 95, 113,
            117, 105, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__316: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__316_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317_value: LeanStringObject<10> =
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
        m_data: [108, 101, 97, 110, 95, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__318_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 115, 108, 105, 99, 101, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__318: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__318_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__319_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 115, 108, 105, 99, 101, 95, 104, 97, 115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__319: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__319_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__320_value: LeanStringObject<11> =
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
        m_data: [108, 101, 97, 110, 95, 115, 111, 114, 114, 121, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__320: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__320_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__321_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 114, 117, 110, 95, 109, 111, 100, 95, 105, 110, 105, 116, 95,
            99, 111, 114, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__321: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__321_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__322_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 95, 102, 111, 114, 103, 101,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__322: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__322_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__323_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 95, 104, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__323: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__323_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__324_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 95, 109, 97, 114, 107, 95,
            109, 117, 108, 116, 105, 95, 116, 104, 114, 101, 97, 100, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__324: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__324_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__325_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 95, 109, 97, 114, 107, 95,
            112, 101, 114, 115, 105, 115, 116, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__325: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__325_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__326_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 115, 97, 114, 114, 97, 121, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__326: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__326_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__327_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 115, 97, 114, 114, 97, 121, 95, 115, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__327: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__327_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328_value: LeanStringObject<53> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 53,
        m_capacity: 53,
        m_length: 52,
        m_data: [
            108, 101, 97, 110, 95, 112, 114, 101, 116, 116, 121, 95, 112, 114, 105, 110, 116, 101,
            114, 95, 102, 111, 114, 109, 97, 116, 116, 101, 114, 95, 105, 110, 116, 101, 114, 112,
            114, 101, 116, 95, 112, 97, 114, 115, 101, 114, 95, 100, 101, 115, 99, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329_value: LeanStringObject<57> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 57,
        m_capacity: 57,
        m_length: 56,
        m_data: [
            108, 101, 97, 110, 95, 112, 114, 101, 116, 116, 121, 95, 112, 114, 105, 110, 116, 101,
            114, 95, 112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 95, 105, 110,
            116, 101, 114, 112, 114, 101, 116, 95, 112, 97, 114, 115, 101, 114, 95, 100, 101, 115,
            99, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__330_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 112, 114, 111, 102, 105, 108, 101, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__330: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__330_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__331_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 112, 116, 114, 95, 97, 100, 100, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__331: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__331_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__332_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 114, 101, 112, 108, 97, 99, 101, 95, 101, 120, 112, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__332: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__332_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__333_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 114, 117, 110, 95, 105, 110, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__333: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__333_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 114, 117, 110, 95, 105, 110, 105, 116, 95, 97, 116, 116, 114,
            115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__335_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 112, 114, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__335: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__335_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__336_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 115, 104, 105, 102, 116, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__336: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__336_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__337_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 115, 104, 105, 102, 116, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__337: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__337_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__338_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 116, 95, 115, 117, 98, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__338: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__338_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__339_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 116, 111, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__339: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__339_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__340_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 111, 112, 116, 105, 111, 110, 95, 103, 101, 116, 95, 111, 114,
            95, 98, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__340: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__340_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__341_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 112, 97, 110, 105, 99, 95, 102, 110, 95, 98, 111, 114, 114, 111,
            119, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__341: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__341_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__342_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 108, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__342: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__342_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__343_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 116, 95, 109, 111, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__343: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__343_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__344_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 116, 95, 109, 117, 108, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__344: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__344_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__345_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 116, 95, 112, 111, 119, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__345: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__345_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__346_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 116, 95, 103, 99, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__346: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__346_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__347_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__347: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__347_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__348_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 108, 111, 103, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__348: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__348_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__349_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 116, 95, 108, 111, 114, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__349: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__349_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__350_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 116, 95, 97, 98, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__350: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__350_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__351_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 116, 95, 97, 100, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__351: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__351_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__352_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__352: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__352_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__353_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__353: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__353_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__354_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__354: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__354_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__355_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 116, 95, 100, 105, 118, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__355: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__355_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__356_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 110, 97, 116, 95, 100, 105, 118, 95, 101, 120, 97, 99, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__356: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__356_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 97, 110, 116, 105, 113, 117, 111, 116, 95, 112,
            97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__358_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 97, 114, 114, 97, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__358: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__358_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__359_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 97, 114, 114, 97,
            121, 95, 119, 105, 116, 104, 95, 99, 97, 112, 97, 99, 105, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__359: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__359_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__360_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 98, 121, 116, 101,
            95, 97, 114, 114, 97, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__360: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__360_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__361_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 102, 108, 111, 97,
            116, 95, 97, 114, 114, 97, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__361: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__361_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__362_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 116, 104, 117, 110, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__362: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__362_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__363_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 101, 113, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__363: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__363_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__364_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 116, 121, 112, 101, 95, 111, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__364: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__364_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__365_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 118, 101, 114, 105, 102, 121, 95, 109,
            111, 100, 117, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__365: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__365_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__366_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 118, 111, 105, 100, 95, 116, 121, 112,
            101, 95, 105, 110, 95, 99, 111, 110, 116, 101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__366: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__366_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__367_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 119, 114, 105, 116, 101, 95, 98, 105,
            116, 99, 111, 100, 101, 95, 116, 111, 95, 102, 105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__367: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__367_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__368_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 109, 97, 110, 117, 97, 108, 95, 103, 101, 116, 95, 114, 111,
            111, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__368: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__368_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__369_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 109, 97, 120, 95, 115, 109, 97, 108, 108, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__369: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__369_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 97, 110, 116, 105, 113, 117, 111, 116, 95, 102,
            111, 114, 109, 97, 116, 116, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__371_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 114, 105, 110, 116, 95, 109, 111,
            100, 117, 108, 101, 95, 116, 111, 95, 115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__371: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__371_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__372_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 100, 108, 108, 95,
            115, 116, 111, 114, 97, 103, 101, 95, 99, 108, 97, 115, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__372: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__372_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__373_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 105, 110, 105, 116,
            105, 97, 108, 105, 122, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__373: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__373_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__374_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 108, 105, 110, 107,
            97, 103, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__374: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__374_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__375_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 116, 97, 105, 108,
            95, 99, 97, 108, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__375: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__375_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__376_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 118, 105, 115, 105,
            98, 105, 108, 105, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__376: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__376_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__377_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 116, 97, 114, 103, 101, 116, 95, 109,
            97, 99, 104, 105, 110, 101, 95, 101, 109, 105, 116, 95, 116, 111, 95, 102, 105, 108,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__377: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__377_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__378_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 109, 111, 100, 117, 108, 101, 95, 116,
            111, 95, 115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__378: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__378_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__379_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 111, 112, 97, 113, 117, 101, 95, 112,
            111, 105, 110, 116, 101, 114, 95, 116, 121, 112, 101, 95, 105, 110, 95, 99, 111, 110,
            116, 101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__379: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__379_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__380_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 97, 114, 115, 101, 95, 98, 105,
            116, 99, 111, 100, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__380: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__380_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__381_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 111, 105, 110, 116, 101, 114, 95,
            116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__381: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__381_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__382_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 111, 115, 105, 116, 105, 111, 110,
            95, 98, 117, 105, 108, 100, 101, 114, 95, 97, 116, 95, 101, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__382: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__382_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__383_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 111, 115, 105, 116, 105, 111, 110,
            95, 98, 117, 105, 108, 100, 101, 114, 95, 98, 101, 102, 111, 114, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__383: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__383_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__384_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 114, 105, 110, 116, 95, 109, 111,
            100, 117, 108, 101, 95, 116, 111, 95, 102, 105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__384: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__384_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__385_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 110, 101, 120, 116,
            95, 103, 108, 111, 98, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__385: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__385_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__386_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 116, 97, 114, 103,
            101, 116, 95, 102, 114, 111, 109, 95, 116, 114, 105, 112, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__386: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__386_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__387_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 117, 110, 100, 101,
            102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__387: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__387_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__388_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 118, 97, 108, 117,
            101, 95, 110, 97, 109, 101, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__388: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__388_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__389_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 105, 110, 105, 116, 105, 97, 108, 105,
            122, 101, 95, 116, 97, 114, 103, 101, 116, 95, 105, 110, 102, 111, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__389: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__389_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__390_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 105, 110, 116, 95, 116, 121, 112, 101,
            95, 105, 110, 95, 99, 111, 110, 116, 101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__390: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__390_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__391_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 108, 105, 110, 107, 95, 109, 111, 100,
            117, 108, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__391: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__391_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__392_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 102, 105, 114, 115,
            116, 95, 102, 117, 110, 99, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__392: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__392_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__393_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 102, 105, 114, 115,
            116, 95, 103, 108, 111, 98, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__393: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__393_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__394_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 102, 105, 114, 115,
            116, 95, 105, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__394: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__394_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__395_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 105, 110, 115, 101,
            114, 116, 95, 98, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__395: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__395_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__396_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 110, 97, 109, 101,
            100, 95, 102, 117, 110, 99, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__396: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__396_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__397_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 110, 97, 109, 101,
            100, 95, 103, 108, 111, 98, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__397: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__397_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__398_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 110, 101, 120, 116,
            95, 102, 117, 110, 99, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__398: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__398_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__399_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 102, 117, 110, 99, 116, 105, 111, 110,
            95, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__399: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__399_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__400_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 98, 97, 115, 105, 99,
            95, 98, 108, 111, 99, 107, 95, 112, 97, 114, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__400: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__400_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__401_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 100, 101, 102, 97,
            117, 108, 116, 95, 116, 97, 114, 103, 101, 116, 95, 116, 114, 105, 112, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__401: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__401_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__402_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 101, 110, 116, 114,
            121, 95, 98, 97, 115, 105, 99, 95, 98, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__402: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__402_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__403_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 100, 105, 115, 112, 111, 115, 101, 95,
            109, 111, 100, 117, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__403: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__403_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__404_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 100, 105, 115, 112, 111, 115, 101, 95,
            116, 97, 114, 103, 101, 116, 95, 109, 97, 99, 104, 105, 110, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__404: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__404_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__405_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 100, 111, 117, 98, 108, 101, 95, 116,
            121, 112, 101, 95, 105, 110, 95, 99, 111, 110, 116, 101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__405: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__405_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__406_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 102, 108, 111, 97, 116, 95, 116, 121,
            112, 101, 95, 105, 110, 95, 99, 111, 110, 116, 101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__406: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__406_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__407_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 111, 117, 110, 116, 95, 98, 97, 115,
            105, 99, 95, 98, 108, 111, 99, 107, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__407: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__407_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__408_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 114, 101, 97, 116, 101, 95, 98, 117,
            105, 108, 100, 101, 114, 95, 105, 110, 95, 99, 111, 110, 116, 101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__408: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__408_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__409_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 114, 101, 97, 116, 101, 95, 99, 111,
            110, 116, 101, 120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__409: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__409_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__410_value: LeanStringObject<53> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 53,
        m_capacity: 53,
        m_length: 52,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 114, 101, 97, 116, 101, 95, 109,
            101, 109, 111, 114, 121, 95, 98, 117, 102, 102, 101, 114, 95, 119, 105, 116, 104, 95,
            99, 111, 110, 116, 101, 110, 116, 115, 95, 111, 102, 95, 102, 105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__410: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__410_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__411_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 114, 101, 97, 116, 101, 95, 109,
            111, 100, 117, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__411: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__411_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__412_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 114, 101, 97, 116, 101, 95, 115,
            116, 114, 105, 110, 103, 95, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__412: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__412_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__413_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 114, 101, 97, 116, 101, 95, 116, 97,
            114, 103, 101, 116, 95, 109, 97, 99, 104, 105, 110, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__413: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__413_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__414_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 117, 110,
            114, 101, 97, 99, 104, 97, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__414: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__414_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__415_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 122, 101,
            120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__415: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__415_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__416_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 108, 101, 97, 114, 95, 105, 110,
            115, 101, 114, 116, 105, 111, 110, 95, 112, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__416: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__416_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__417_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 111, 110, 115, 116, 95, 97, 114,
            114, 97, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__417: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__417_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__418_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 111, 110, 115, 116, 95, 105, 110,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__418: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__418_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__419_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 111, 110, 115, 116, 95, 112, 111,
            105, 110, 116, 101, 114, 95, 110, 117, 108, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__419: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__419_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__420_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 111, 110, 115, 116, 95, 115, 116,
            114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__420: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__420_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__421_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 112, 116,
            114, 95, 116, 111, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__421: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__421_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__422_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 114, 101,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__422: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__422_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__423_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 101,
            120, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__423: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__423_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__424_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 101,
            120, 116, 95, 111, 114, 95, 116, 114, 117, 110, 99, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__424: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__424_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__425_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 116,
            111, 114, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__425: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__425_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__426_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 117,
            98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__426: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__426_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__427_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 119,
            105, 116, 99, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__427: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__427_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__428_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 103, 101,
            112, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__428: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__428_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__429_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 103, 108,
            111, 98, 97, 108, 95, 115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__429: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__429_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__430_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 105, 99,
            109, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__430: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__430_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__431_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 105, 110,
            98, 111, 117, 110, 100, 115, 95, 103, 101, 112, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__431: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__431_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__432_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 108, 111,
            97, 100, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__432: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__432_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__433_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 109, 117,
            108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__433: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__433_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__434_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 110, 111,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__434: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__434_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__435_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 97, 112, 112, 101, 110, 100, 95, 98, 97,
            115, 105, 99, 95, 98, 108, 111, 99, 107, 95, 105, 110, 95, 99, 111, 110, 116, 101, 120,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__435: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__435_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__436_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 97, 114, 114, 97, 121, 95, 116, 121,
            112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__436: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__436_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__437_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 97, 100,
            100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__437: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__437_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__438_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 97, 108,
            108, 111, 99, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__438: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__438_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__439_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 98, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__439: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__439_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__440_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 99, 97, 108,
            108, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__440: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__440_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__441_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 99, 111,
            110, 100, 95, 98, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__441: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__441_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__442_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__442: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__442_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__443_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 109, 107, 95, 100, 97, 116, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__443: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__443_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__444_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 108, 105, 98, 117, 118, 95, 118, 101, 114, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__444: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__444_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__445_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 97, 100, 100, 95, 97, 116, 116, 114,
            105, 98, 117, 116, 101, 95, 97, 116, 95, 105, 110, 100, 101, 120, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__445: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__445_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__446_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 97, 100, 100, 95, 99, 97, 115, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__446: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__446_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__447_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 97, 100, 100, 95, 102, 117, 110, 99,
            116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__447: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__447_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__448_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 97, 100, 100, 95, 103, 108, 111, 98, 97,
            108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__448: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__448_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__449_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 105, 110, 116, 51,
            50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__449: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__449_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__450_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 105, 110, 116, 54,
            52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__450: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__450_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__451_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 105, 110, 116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__451: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__451_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__452_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__452: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__452_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__453_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 99, 104, 101, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__453: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__453_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__454_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 105, 115, 95, 100, 101, 102,
            95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__454: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__454_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__455_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 119, 104, 110, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__455: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__455_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__456_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__456: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__456_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__457_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__457: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__457_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__458_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__458: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__458_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__459_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 105, 110, 116, 49,
            54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__459: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__459_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__460_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__460: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__460_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__461_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 115, 104, 105, 102, 116, 95, 108,
            101, 102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__461: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__461_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__462_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 115, 104, 105, 102, 116, 95, 114,
            105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__462: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__462_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__463_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__463: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__463_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__464_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__464: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__464_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__465_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__465: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__465_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__466_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__466: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__466_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__467_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__467: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__467_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__468_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__468: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__468_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__469_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__469: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__469_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__470_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 111, 102, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__470: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__470_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__471_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 115, 99, 97, 108, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__471: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__471_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__472_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 97, 98, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__472: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__472_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__473_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__473: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__473_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__474_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 99, 111, 109, 112, 108, 101, 109,
            101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__474: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__474_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__475_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__475: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__475_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__476_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__476: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__476_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__477_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__477: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__477_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__478_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 105, 111, 95, 119, 97, 105, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__478: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__478_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__479_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 119, 97, 105, 116, 95, 97, 110, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__479: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__479_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 114, 95, 101, 120, 112, 111, 114, 116, 95, 101, 110, 116,
            114, 105, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__481_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 101, 120, 99, 108, 117, 115, 105, 118, 101, 95,
            111, 98, 106, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__481: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__481_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 101, 120, 112, 114, 95, 100, 101, 102, 95, 101,
            113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 108, 101, 118, 101, 108, 95, 100, 101, 102, 95,
            101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 114, 101, 115, 101, 114, 118, 101, 100, 95, 110,
            97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__485_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 114, 101, 97, 108, 112, 97, 116, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__485: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__485_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__486_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 114, 101, 109, 111, 118, 101, 95, 100, 105, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__486: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__486_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__487_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 114, 101, 109, 111, 118, 101, 95, 102, 105, 108,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__487: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__487_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__488_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 114, 101, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__488: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__488_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__489_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 115, 101, 116, 95, 104, 101, 97, 114, 116, 98,
            101, 97, 116, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__489: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__489_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__490_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 115, 121, 109, 108, 105, 110, 107, 95, 109, 101,
            116, 97, 100, 97, 116, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__490: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__490_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__491_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 116, 105, 109, 101, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__491: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__491_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__492_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 103, 101,
            116, 95, 112, 105, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__492: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__492_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__493_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 115, 101,
            116, 95, 99, 117, 114, 114, 101, 110, 116, 95, 100, 105, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__493: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__493_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__494_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 115, 112,
            97, 119, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__494: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__494_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__495_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 109, 105, 115, 101, 95, 110, 101,
            119, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__495: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__495_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__496_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 109, 105, 115, 101, 95, 114, 101,
            115, 111, 108, 118, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__496: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__496_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__497_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 109, 105, 115, 101, 95, 114, 101,
            115, 117, 108, 116, 95, 111, 112, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__497: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__497_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__498_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 114, 101, 97, 100, 95, 100, 105, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__498: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__498_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__499_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 119, 114, 105, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__499: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__499_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__500_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104,
            105, 108, 100, 95, 107, 105, 108, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__500: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__500_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__501_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104,
            105, 108, 100, 95, 112, 105, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__501: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__501_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__502_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104,
            105, 108, 100, 95, 116, 97, 107, 101, 95, 115, 116, 100, 105, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__502: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__502_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__503_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104,
            105, 108, 100, 95, 116, 114, 121, 95, 119, 97, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__503: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__503_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__504_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104,
            105, 108, 100, 95, 119, 97, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__504: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__504_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__505_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 103, 101,
            116, 95, 99, 117, 114, 114, 101, 110, 116, 95, 100, 105, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__505: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__505_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__506_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__506: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__506_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__507_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 112, 117, 116, 95, 115, 116, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__507: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__507_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__508_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 114, 101, 97, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__508: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__508_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__509_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 114, 101, 119, 105, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__509: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__509_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__510_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 116, 114, 117, 110, 99, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__510: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__510_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__511_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 116, 114, 121, 95, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__511: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__511_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__512_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 117, 110, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__512: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__512_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__513_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 102, 108, 117, 115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__513: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__513_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__514_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 103, 101, 116, 95, 108, 105, 110, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__514: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__514_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__515_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 105, 115, 95, 116, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__515: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__515_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__516_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108,
            101, 95, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__516: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__516_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__517_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 109, 97, 112, 95, 116, 97, 115, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__517: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__517_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__518_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 109, 101, 116, 97, 100, 97, 116, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__518: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__518_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__519_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 109, 111, 110, 111, 95, 109, 115, 95, 110, 111,
            119, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__519: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__519_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__520_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 109, 111, 110, 111, 95, 110, 97, 110, 111, 115,
            95, 110, 111, 119, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__520: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__520_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__521_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 103, 101, 116, 95, 110, 117, 109, 95, 104, 101,
            97, 114, 116, 98, 101, 97, 116, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__521: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__521_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__522_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 103, 101, 116, 95, 114, 97, 110, 100, 111, 109,
            95, 98, 121, 116, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__522: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__522_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__523_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 103, 101, 116, 95, 116, 97, 115, 107, 95, 115,
            116, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__523: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__523_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__524_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 103, 101, 116, 95, 116, 105, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__524: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__524_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__525_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 103, 101, 116, 101, 110, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__525: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__525_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__526_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 104, 97, 114, 100, 95, 108, 105, 110, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__526: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__526_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__527_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 105, 110, 105, 116, 105, 97, 108, 105, 122, 105,
            110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__527: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__527_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__528_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 111, 110, 100, 118, 97, 114, 95, 119, 97, 105,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__528: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__528_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__529_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 114, 101, 97, 116, 101, 95, 100, 105, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__529: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__529_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__530_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 114, 101, 97, 116, 101, 95, 116, 101, 109,
            112, 100, 105, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__530: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__530_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__531_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 114, 101, 97, 116, 101, 95, 116, 101, 109,
            112, 102, 105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__531: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__531_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__532_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 117, 114, 114, 101, 110, 116, 95, 100, 105,
            114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__532: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__532_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__533_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 105, 111, 95, 101, 120, 105, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__533: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__533_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__534_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 102, 111, 114, 99, 101, 95, 101, 120, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__534: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__534_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__535_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100,
            109, 117, 116, 101, 120, 95, 119, 114, 105, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__535: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__535_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__536_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 105, 110, 100, 95, 116, 97, 115, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__536: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__536_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__537_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 97, 110, 99, 101, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__537: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__537_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__538_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 104, 101, 99, 107, 95, 99, 97, 110, 99, 101,
            108, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__538: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__538_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__539_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 111, 110, 100, 118, 97, 114, 95, 110, 101,
            119, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__539: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__539_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__540_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 111, 110, 100, 118, 97, 114, 95, 110, 111,
            116, 105, 102, 121, 95, 97, 108, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__540: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__540_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__541_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 111, 110, 100, 118, 97, 114, 95, 110, 111,
            116, 105, 102, 121, 95, 111, 110, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__541: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__541_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__542_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 114, 101, 99, 109, 117, 116,
            101, 120, 95, 117, 110, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__542: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__542_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__543_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100,
            109, 117, 116, 101, 120, 95, 110, 101, 119, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__543: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__543_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__544_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100,
            109, 117, 116, 101, 120, 95, 114, 101, 97, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__544: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__544_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__545_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100,
            109, 117, 116, 101, 120, 95, 116, 114, 121, 95, 114, 101, 97, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__545: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__545_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__546_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100,
            109, 117, 116, 101, 120, 95, 116, 114, 121, 95, 119, 114, 105, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__546: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__546_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__547_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100,
            109, 117, 116, 101, 120, 95, 117, 110, 108, 111, 99, 107, 95, 114, 101, 97, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__547: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__547_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__548_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100,
            109, 117, 116, 101, 120, 95, 117, 110, 108, 111, 99, 107, 95, 119, 114, 105, 116, 101,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__548: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__548_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__549_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 109, 117, 116, 101, 120, 95,
            108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__549: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__549_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__550_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 109, 117, 116, 101, 120, 95,
            110, 101, 119, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__550: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__550_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__551_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 109, 117, 116, 101, 120, 95,
            116, 114, 121, 95, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__551: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__551_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__552_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 109, 117, 116, 101, 120, 95,
            117, 110, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__552: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__552_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__553_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 114, 101, 99, 109, 117, 116,
            101, 120, 95, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__553: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__553_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__554_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 114, 101, 99, 109, 117, 116,
            101, 120, 95, 110, 101, 119, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__554: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__554_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__555_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 114, 101, 99, 109, 117, 116,
            101, 120, 95, 116, 114, 121, 95, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__555: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__555_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__556_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 115, 101, 116, 95,
            101, 120, 105, 116, 95, 111, 110, 95, 112, 97, 110, 105, 99, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__556: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__556_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__557_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 115, 101, 116, 95,
            109, 97, 120, 95, 104, 101, 97, 114, 116, 98, 101, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__557: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__557_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__558_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 115, 101, 116, 95,
            109, 97, 120, 95, 109, 101, 109, 111, 114, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__558: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__558_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__559_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 115, 101, 116, 95,
            116, 104, 114, 101, 97, 100, 95, 115, 116, 97, 99, 107, 95, 115, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__559: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__559_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__560_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 97, 108, 108, 111, 99, 112, 114, 111, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__560: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__560_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__561_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 97, 112, 112, 95, 112, 97, 116, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__561: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__561_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__562_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 97, 115, 95, 116, 97, 115, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__562: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__562_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__563_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95,
            100, 101, 102, 97, 117, 108, 116, 95, 118, 101, 114, 98, 111, 115, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__563: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__563_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__564_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95,
            104, 97, 114, 100, 119, 97, 114, 101, 95, 99, 111, 110, 99, 117, 114, 114, 101, 110,
            99, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__564: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__564_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__565_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 104, 97, 115, 95, 97,
            100, 100, 114, 101, 115, 115, 95, 115, 97, 110, 105, 116, 105, 122, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__565: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__565_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__566_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 104, 97, 115, 95,
            108, 108, 118, 109, 95, 98, 97, 99, 107, 101, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__566: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__566_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__567_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 105, 115, 95, 100,
            101, 98, 117, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__567: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__567_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__568_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 105, 115, 95, 109,
            117, 108, 116, 105, 95, 116, 104, 114, 101, 97, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__568: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__568_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__569_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 105, 115, 95, 115,
            116, 97, 103, 101, 48, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__569: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__569_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__570_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95,
            98, 117, 105, 108, 100, 95, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__570: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__570_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__571_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95,
            100, 101, 102, 97, 117, 108, 116, 95, 109, 97, 120, 95, 104, 101, 97, 114, 116, 98,
            101, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__571: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__571_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__572_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95,
            100, 101, 102, 97, 117, 108, 116, 95, 109, 97, 120, 95, 109, 101, 109, 111, 114, 121,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__572: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__572_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__573_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95,
            100, 101, 102, 97, 117, 108, 116, 95, 111, 112, 116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__573: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__573_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__574_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 116, 111, 95, 105, 115, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__574: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__574_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__575_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__575: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__575_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__576_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 101, 110, 97, 98,
            108, 101, 95, 100, 101, 98, 117, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__576: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__576_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__577_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95,
            98, 101, 108, 105, 101, 118, 101, 114, 95, 116, 114, 117, 115, 116, 95, 108, 101, 118,
            101, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__577: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__577_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__578_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__578: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__578_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__579_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 116, 111, 95, 102, 108, 111, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__579: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__579_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__580_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 116, 111, 95, 102, 108, 111, 97, 116, 51,
            50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__580: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__580_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__581_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 116, 111, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__581: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__581_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__582_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 116, 111, 95, 105, 110, 116, 49, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__582: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__582_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__583_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 116, 111, 95, 105, 110, 116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__583: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__583_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__584_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 116, 111, 95, 105, 110, 116, 54, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__584: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__584_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__585_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__585: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__585_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__586_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__586: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__586_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__587_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__587: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__587_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__588_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 111, 102, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__588: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__588_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__589_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__589: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__589_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__590_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 115, 104, 105, 102, 116, 95, 108, 101,
            102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__590: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__590_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__591_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 115, 104, 105, 102, 116, 95, 114, 105,
            103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__591: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__591_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__592_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 99, 111, 109, 112, 108, 101, 109, 101,
            110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__592: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__592_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__593_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__593: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__593_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__594_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__594: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__594_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__595_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__595: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__595_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__596_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__596: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__596_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__597_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__597: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__597_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__598_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__598: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__598_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__599_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 105, 110, 116, 49, 54,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__599: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__599_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__600_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 105, 110, 116, 51, 50,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__600: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__600_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__601_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 105, 110, 116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__601: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__601_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__602_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 105, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__602: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__602_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__603_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__603: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__603_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__604_value: LeanStringObject<14> =
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
        m_data: [108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 97, 98, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__604: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__604_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__605_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__605: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__605_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__606_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__606: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__606_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__607_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 115, 104, 105, 102, 116, 95, 108,
            101, 102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__607: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__607_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__608_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 115, 104, 105, 102, 116, 95, 114,
            105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__608: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__608_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__609_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__609: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__609_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__610_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 102, 108, 111, 97, 116,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__610: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__610_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__611_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 102, 108, 111, 97, 116,
            51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__611: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__611_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__612_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 105, 110, 116, 95, 115,
            105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__612: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__612_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__613_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__613: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__613_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__614_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__614: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__614_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__615_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__615: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__615_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__616_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__616: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__616_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__617_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__617: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__617_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__618_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__618: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__618_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__619_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 111, 102, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__619: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__619_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__620_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__620: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__620_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__621_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 97, 98, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__621: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__621_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__622_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__622: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__622_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__623_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 99, 111, 109, 112, 108, 101, 109,
            101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__623: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__623_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__624_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__624: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__624_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__625_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__625: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__625_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__626_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__626: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__626_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__627_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 49, 54,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__627: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__627_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__628_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 54, 52,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__628: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__628_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__629_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__629: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__629_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__630_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 105, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__630: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__630_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__631_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__631: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__631_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__632_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 102, 108, 111, 97, 116,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__632: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__632_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__633_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 102, 108, 111, 97, 116,
            51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__633: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__633_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__634_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__634: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__634_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__635_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__635: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__635_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__636_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__636: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__636_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__637_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__637: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__637_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__638_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 111, 102, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__638: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__638_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__639_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__639: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__639_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__640_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 115, 104, 105, 102, 116, 95, 108,
            101, 102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__640: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__640_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__641_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 115, 104, 105, 102, 116, 95, 114,
            105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__641: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__641_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__642_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 99, 111, 109, 112, 108, 101, 109,
            101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__642: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__642_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__643_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__643: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__643_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__644_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__644: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__644_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__645_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__645: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__645_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__646_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__646: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__646_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__647_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__647: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__647_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__648_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__648: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__648_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__649_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 105, 110, 116, 51, 50,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__649: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__649_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__650_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 105, 110, 116, 54, 52,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__650: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__650_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__651_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 105, 110, 116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__651: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__651_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__652_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 105, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__652: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__652_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__653_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 120, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__653: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__653_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__654_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 97, 98, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__654: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__654_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__655_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__655: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__655_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__656_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__656: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__656_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__657_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 115, 104, 105, 102, 116, 95, 108,
            101, 102, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__657: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__657_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__658_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 115, 104, 105, 102, 116, 95, 114,
            105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__658: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__658_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__659_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__659: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__659_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__660_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 102, 108, 111, 97, 116,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__660: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__660_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__661_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 102, 108, 111, 97, 116,
            51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__661: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__661_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__662_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__662: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__662_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__663_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__663: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__663_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__664_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 108, 97, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__664: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__664_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__665_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 108, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__665: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__665_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__666_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__666: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__666_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__667_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__667: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__667_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__668_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__668: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__668_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__669_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 111, 102, 95, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__669: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__669_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__670_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 105, 110, 116, 95, 115, 117, 98, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__670: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__670_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__671_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 97, 98, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__671: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__671_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__672_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__672: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__672_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__673_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 99, 111, 109, 112, 108, 101, 109,
            101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__673: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__673_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__674_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__674: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__674_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__675_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__675: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__675_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__676_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__676: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__676_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__677_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 95, 100, 105, 118, 95, 101, 120, 97, 99, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__677: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__677_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__678_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 95, 101, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__678: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__678_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__679_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 95, 101, 109, 111, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__679: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__679_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__680_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 105, 110, 116, 95, 109, 111, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__680: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__680_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__681_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 105, 110, 116, 95, 109, 117, 108, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__681: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__681_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__682_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 105, 110, 116, 95, 110, 101, 103, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__682: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__682_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__683_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 95, 110, 101, 103, 95, 115, 117, 99, 99, 95, 111,
            102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__683: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__683_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__684_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 95, 100, 101, 99, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__684: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__684_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__685_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 95, 100, 101, 99, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__685: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__685_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__686_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 95, 100, 101, 99, 95, 110, 111, 110, 110, 101,
            103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__686: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__686_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__687_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 105, 110, 116, 95, 100, 105, 118, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__687: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__687_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__688_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 95, 101,
            120, 112, 114, 95, 109, 118, 97, 114, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__688: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__688_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__689_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 95, 108,
            101, 118, 101, 108, 95, 109, 118, 97, 114, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__689: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__689_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__690_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 105, 110, 116, 95, 97, 100, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__690: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__690_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__691_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 110, 116, 95, 100, 101, 99, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__691: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__691_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 110, 111, 114, 109, 97, 108, 105,
            122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 112, 114, 101, 112, 114, 111, 99,
            101, 115, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 112, 114, 111, 99, 101, 115, 115,
            95, 110, 101, 119, 95, 102, 97, 99, 116, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 104, 97, 115, 95, 99, 111, 109, 112, 105, 108, 101, 95, 101,
            114, 114, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 100, 98, 103, 95, 99, 108, 105, 101, 110, 116, 95, 108,
            111, 111, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 110, 102, 101, 114, 95, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__698_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 110, 105, 116, 95, 108, 108, 118, 109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__698: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__698_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__699_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            108, 101, 97, 110, 95, 103, 101, 116, 95, 119, 105, 110, 100, 111, 119, 115, 95, 108,
            111, 99, 97, 108, 95, 116, 105, 109, 101, 122, 111, 110, 101, 95, 105, 100, 95, 97,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__699: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__699_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 99, 117, 116, 115, 97, 116, 95, 97,
            115, 115, 101, 114, 116, 95, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 99, 117, 116, 115, 97, 116, 95, 97,
            115, 115, 101, 114, 116, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 99, 117, 116, 115, 97, 116, 95,
            109, 107, 95, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 105, 110, 116, 101, 114, 110, 97,
            108, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 109, 107, 95, 101, 113, 95, 112,
            114, 111, 111, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 109, 107, 95, 104, 101, 113, 95,
            112, 114, 111, 111, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__706_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 101, 116, 95, 115, 116, 100, 105, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__706: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__706_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__707_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 101, 116, 95, 115, 116, 100, 111, 117,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__707: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__707_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__708_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 116, 100, 101, 114, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__708: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__708_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__709_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 116, 100, 105, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__709: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__709_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__710_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 116, 100, 111, 117, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__710: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__710_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 116, 114, 117, 99, 116, 117, 114, 97,
            108, 95, 114, 101, 99, 95, 97, 114, 103, 95, 112, 111, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__712_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 117, 115, 105, 122, 101, 95, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__712: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__712_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__713_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 108, 105, 110, 107, 101, 114, 95, 102, 108,
            97, 103, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__713: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__713_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 109, 97, 116, 99, 104, 95, 101, 113, 117, 97,
            116, 105, 111, 110, 115, 95, 102, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__715_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 109, 97, 120, 95, 99, 116, 111, 114, 95, 102,
            105, 101, 108, 100, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__715: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__715_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__716_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 103, 101, 116, 95, 109, 97, 120, 95, 99, 116, 111, 114, 95, 115,
            99, 97, 108, 97, 114, 115, 95, 115, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__716: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__716_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__717_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 109, 97, 120, 95, 99, 116, 111, 114, 95, 116,
            97, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__717: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__717_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 110, 117, 109, 95, 97, 116, 116, 114, 105,
            98, 117, 116, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__719_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 101, 116, 95, 115, 116, 100, 101, 114,
            114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__719: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__719_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 99, 111, 110, 103, 114, 95, 109, 97, 116, 99,
            104, 95, 101, 113, 117, 97, 116, 105, 111, 110, 115, 95, 102, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__721_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 99, 117, 114, 114, 101, 110, 116, 95, 116,
            105, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__721: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__721_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__722_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 103, 105, 116, 104, 97, 115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__722: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__722_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__723_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 103, 101, 116, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95,
            108, 105, 110, 107, 101, 114, 95, 102, 108, 97, 103, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__723: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__723_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 105, 114, 95, 101, 120, 116, 114, 97, 95, 99,
            111, 110, 115, 116, 95, 110, 97, 109, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__725_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 108, 101, 97, 110, 99, 95, 101, 120, 116,
            114, 97, 95, 102, 108, 97, 103, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__725: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__725_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__726_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 108, 101, 97, 110, 99, 95, 105, 110, 116,
            101, 114, 110, 97, 108, 95, 102, 108, 97, 103, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__726: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__726_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__727_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 105, 115, 105,
            122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__727: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__727_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__728_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 115, 116, 114,
            105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__728: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__728_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__729_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110,
            116, 49, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__729: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__729_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__730_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__730: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__730_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__731_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110,
            116, 54, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__731: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__731_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__732_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110,
            116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__732: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__732_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__733_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 117, 115, 105,
            122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__733: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__733_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__734_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__734: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__734_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__735_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 98, 105, 116,
            115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__735: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__735_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__736_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 102, 108, 111,
            97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__736: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__736_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__737_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116,
            49, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__737: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__737_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__738_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116,
            51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__738: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__738_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__739_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116,
            54, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__739: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__739_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__740_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116,
            56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__740: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__740_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__741_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__741: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__741_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__742_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 110, 101, 103, 97, 116, 101,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__742: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__742_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__743_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 111, 102, 95, 98, 105, 116,
            115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__743: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__743_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__744_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 115, 99, 97, 108, 101, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__744: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__744_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__745_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 102, 114, 101, 120, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__745: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__745_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__746_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 105, 115, 102, 105, 110,
            105, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__746: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__746_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__747_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 105, 115, 105, 110, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__747: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__747_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__748_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 105, 115, 110, 97, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__748: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__748_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__749_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 105, 110, 116,
            56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__749: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__749_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__750_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__750: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__750_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__751_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__751: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__751_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__752_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 98, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__752: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__752_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__753_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 100, 101, 99, 76, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__753: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__753_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__754_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 100, 101, 99, 76, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__754: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__754_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__755_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__755: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__755_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__756_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 105, 110, 116, 54, 52,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__756: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__756_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__757_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 105, 110, 116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__757: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__757_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__758_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 105, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__758: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__758_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__759_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 115, 116, 114, 105,
            110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__759: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__759_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__760_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 105, 110, 116,
            49, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__760: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__760_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__761_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 105, 110, 116,
            51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__761: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__761_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__762_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 105, 110, 116,
            54, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__762: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__762_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__763_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 111, 102, 95, 98, 105, 116, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__763: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__763_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__764_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 115, 99, 97, 108, 101, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__764: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__764_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__765_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 115, 117, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__765: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__765_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__766_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 98, 105, 116, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__766: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__766_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__767_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 102, 108, 111, 97,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__767: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__767_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__768_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 105, 110, 116, 49, 54,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__768: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__768_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__769_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 105, 110, 116, 51, 50,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__769: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__769_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__770_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 100, 105, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__770: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__770_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__771_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 102, 114, 101, 120, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__771: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__771_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__772_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 105, 115, 102, 105, 110, 105, 116,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__772: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__772_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__773_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 105, 115, 105, 110, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__773: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__773_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__774_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 105, 115, 110, 97, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__774: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__774_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__775_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 109, 117, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__775: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__775_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__776_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 110, 101, 103, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__776: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__776_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__777_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 115, 101,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__777: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__777_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__778_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 115, 105,
            122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__778: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__778_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__779_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 117, 103,
            101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__779: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__779_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__780_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 117, 115,
            101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__780: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__780_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__781_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 98, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__781: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__781_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__782_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 100, 101, 99, 76, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__782: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__782_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__783_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 100, 101, 99, 76, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__783: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__783_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__784_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__784: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__784_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__785_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 100, 97,
            116, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__785: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__785_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__786_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 102, 103,
            101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__786: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__786_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__787_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 102, 115,
            101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__787: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__787_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__788_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 103, 101,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__788: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__788_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__789_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 109, 107,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__789: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__789_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__790_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 112, 117,
            115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__790: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__790_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__791_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 108, 111, 119, 101, 114, 95, 108, 111,
            111, 115, 101, 95, 98, 118, 97, 114, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__791: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__791_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__792_value: LeanStringObject<13> =
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
        m_data: [108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 108, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__792: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__792_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__793_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 97, 112, 112, 95, 100, 97,
            116, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__793: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__793_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__794_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 100, 97, 116, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__794: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__794_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__795_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 113, 117, 105, 99, 107, 95, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__795: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__795_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__796_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 102, 105, 110, 100, 95, 101, 120, 112, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__796: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__796_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__797_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 102, 105, 110, 100, 95, 101, 120, 116, 95, 101, 120, 112, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__797: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__797_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__798_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105,
            97, 116, 101, 95, 114, 101, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__798: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__798_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__799_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105,
            97, 116, 101, 95, 114, 101, 118, 95, 114, 97, 110, 103, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__799: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__799_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__800_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105,
            97, 116, 101, 49, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__800: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__800_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__801_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 108, 105, 102, 116, 95, 108, 111, 111,
            115, 101, 95, 98, 118, 97, 114, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__801: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__801_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__802_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 101, 113, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__802: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__802_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__803_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 108, 111, 111, 115,
            101, 95, 98, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__803: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__803_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__804_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105,
            97, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__804: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__804_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__805_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105,
            97, 116, 101, 95, 114, 97, 110, 103, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__805: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__805_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__806_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 101, 118, 97, 108, 95, 109, 97, 105, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__806: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__806_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 101, 118, 97, 108, 95, 115, 117, 103, 103, 101, 115, 116, 95,
            116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__808_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 97, 98, 115, 116, 114, 97, 99, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__808: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__808_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__809_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 97, 98, 115, 116, 114, 97, 99, 116, 95,
            114, 97, 110, 103, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__809: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__809_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__810_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 100, 97, 116, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__810: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__810_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__811_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 100, 98, 103, 95, 116, 111, 95, 115,
            116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__811: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__811_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__812_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 101, 113, 117, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__812: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__812_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__813_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 100, 121, 110, 108, 105, 98, 95, 108, 111, 97, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__813: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__813_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__814_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 100, 121, 110, 108, 105, 98, 95, 115, 121, 109, 98, 111, 108,
            95, 114, 117, 110, 95, 97, 115, 95, 105, 110, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__814: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__814_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__815_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 101, 108, 97, 98, 95, 97, 100, 100, 95, 100, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__815: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__815_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__816_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 101, 108, 97, 98, 95, 97, 100, 100, 95, 100, 101, 99, 108, 95,
            119, 105, 116, 104, 111, 117, 116, 95, 99, 104, 101, 99, 107, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__816: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__816_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__817_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 101, 109, 105, 116, 95, 108, 108, 118, 109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__817: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__817_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 101, 118, 97, 108, 95, 99, 104, 101, 99, 107, 95, 109, 101, 116,
            97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__819_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 101, 118, 97, 108, 95, 99, 111, 110, 115, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__819: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__819_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__820_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 100, 98, 103, 95, 115, 116, 97, 99, 107, 95, 116, 114, 97, 99,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__820: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__820_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__821_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 100, 98, 103, 95, 116, 114, 97, 99, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__821: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__821_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__822_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 100, 98, 103, 95, 116, 114, 97, 99, 101, 95, 105, 102, 95, 115,
            104, 97, 114, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__822: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__822_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__823_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 100, 101, 99, 111, 100, 101, 95, 108, 111, 115, 115, 121, 95,
            117, 116, 102, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__823: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__823_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__824_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            108, 101, 97, 110, 95, 100, 105, 115, 112, 108, 97, 121, 95, 99, 117, 109, 117, 108,
            97, 116, 105, 118, 101, 95, 112, 114, 111, 102, 105, 108, 105, 110, 103, 95, 116, 105,
            109, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__824: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__824_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825_value: LeanStringObject<11> =
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
        m_data: [108, 101, 97, 110, 95, 100, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__826_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 100, 121, 110, 108, 105, 98, 95, 103, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__826: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__826_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__827_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103,
            105, 111, 110, 95, 105, 115, 95, 109, 101, 109, 111, 114, 121, 95, 109, 97, 112, 112,
            101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__827: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__827_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__828_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103,
            105, 111, 110, 95, 114, 101, 97, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__828: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__828_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__829_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103,
            105, 111, 110, 95, 115, 97, 118, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__829: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__829_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__830_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103,
            105, 111, 110, 95, 115, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__830: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__830_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 99, 117, 116, 115, 97, 116, 95, 101, 113, 95, 99, 110, 115, 116,
            114, 95, 116, 111, 95, 112, 114, 111, 111, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 99, 117, 116, 115, 97, 116, 95, 112, 114, 111, 112, 97, 103, 97,
            116, 101, 95, 110, 111, 110, 108, 105, 110, 101, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__833_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 100, 98, 103, 95, 115, 108, 101, 101, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__833: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__833_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__834_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 117, 103, 101,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__834: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__834_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__835_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 117, 115, 101,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__835: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__835_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__836_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 115, 108, 105, 99, 101, 95, 98, 101, 113, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__836: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__836_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 99, 104, 101, 99, 107, 101, 100, 95, 97, 115, 115, 105, 103,
            110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__838_value: LeanStringObject<11> =
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
        m_data: [108, 101, 97, 110, 95, 99, 104, 109, 111, 100, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__838: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__838_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__839_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 99, 108, 111, 115, 117, 114, 101, 95, 109, 97, 120, 95, 97, 114,
            103, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__839: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__839_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__840_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103,
            105, 111, 110, 95, 102, 114, 101, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__840: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__840_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__841_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 102, 115, 101,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__841: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__841_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__842_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 103, 101, 116,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__842: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__842_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__843_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 104, 97, 115,
            104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__843: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__843_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__844_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__844: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__844_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__845_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 112, 117, 115,
            104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__845: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__845_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__846_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 115, 101, 116,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__846: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__846_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__847_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__847: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__847_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__848_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 117, 105, 110, 116, 51, 50,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__848: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__848_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__849_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 117, 105, 110, 116, 54, 52,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__849: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__849_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__850_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 117, 105, 110, 116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__850: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__850_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__851_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 117, 115, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__851: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__851_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__852_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 99, 111, 112,
            121, 95, 115, 108, 105, 99, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__852: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__852_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__853_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 100, 97, 116,
            97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__853: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__853_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__854_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 102, 103, 101,
            116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__854: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__854_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__855_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 117, 115, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__855: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__855_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__856_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 105, 110, 116, 49, 54, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__856: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__856_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__857_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 105, 110, 116, 51, 50, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__857: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__857_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__858_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 105, 110, 116, 54, 52, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__858: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__858_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__859_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 105, 110, 116, 56, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__859: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__859_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__860_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 105, 115, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__860: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__860_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__861_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 117, 105, 110, 116, 49, 54,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__861: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__861_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__862_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 112, 117, 115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__862: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__862_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__863_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 115, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__863: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__863_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__864_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 115, 105, 122, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__864: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__864_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__865_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 115, 119, 97, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__865: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__865_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__866_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 116, 111, 95, 108, 105, 115, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__866: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__866_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__867_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 117, 103, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__867: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__867_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__868_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 117, 103, 101, 116, 95, 98, 111, 114,
            114, 111, 119, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__868: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__868_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__869_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 102, 115, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__869: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__869_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__870_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 102, 115, 119, 97, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__870: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__870_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__871_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 103, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__871: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__871_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__872_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 103, 101, 116, 95, 98, 111, 114, 114,
            111, 119, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__872: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__872_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__873_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 103, 101, 116, 95, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__873: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__873_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__874_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__874: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__874_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__875_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 112, 111, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__875: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__875_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__876_value: LeanStringObject<6> =
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
        m_data: [102, 108, 111, 111, 114, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__876: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__876_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__877_value: LeanStringObject<7> =
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
        m_data: [102, 108, 111, 111, 114, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__877: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__877_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878_value: LeanStringObject<21> =
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
            108, 97, 107, 101, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 97,
            100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__879_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 97, 100, 100, 95, 100, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__879: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__879_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__880_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 97, 100, 100, 95, 100, 101, 99, 108, 95, 119, 105, 116, 104,
            111, 117, 116, 95, 99, 104, 101, 99, 107, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__880: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__880_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__881_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 102, 103, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__881: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__881_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__882_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 102, 103, 101, 116, 95, 98, 111, 114,
            114, 111, 119, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__882: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__882_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__883_value: LeanStringObject<6> =
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
        m_data: [99, 111, 115, 104, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__883: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__883_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__884_value: LeanStringObject<4> =
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
        m_data: [101, 120, 112, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__884: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__884_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__885_value: LeanStringObject<5> =
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
        m_data: [101, 120, 112, 50, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__885: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__885_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__886_value: LeanStringObject<6> =
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
        m_data: [101, 120, 112, 50, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__886: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__886_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__887_value: LeanStringObject<5> =
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
        m_data: [101, 120, 112, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__887: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__887_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__888_value: LeanStringObject<5> =
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
        m_data: [102, 97, 98, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__888: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__888_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__889_value: LeanStringObject<6> =
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
        m_data: [102, 97, 98, 115, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__889: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__889_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__890_value: LeanStringObject<5> =
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
        m_data: [99, 98, 114, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__890: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__890_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__891_value: LeanStringObject<6> =
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
        m_data: [99, 98, 114, 116, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__891: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__891_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__892_value: LeanStringObject<5> =
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
        m_data: [99, 101, 105, 108, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__892: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__892_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__893_value: LeanStringObject<6> =
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
        m_data: [99, 101, 105, 108, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__893: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__893_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__894_value: LeanStringObject<4> =
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
        m_data: [99, 111, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__894: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__894_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__895_value: LeanStringObject<5> =
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
        m_data: [99, 111, 115, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__895: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__895_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__896_value: LeanStringObject<5> =
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
        m_data: [99, 111, 115, 104, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__896: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__896_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__897_value: LeanStringObject<7> =
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
        m_data: [97, 115, 105, 110, 104, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__897: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__897_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__898_value: LeanStringObject<5> =
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
        m_data: [97, 116, 97, 110, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__898: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__898_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__899_value: LeanStringObject<6> =
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
        m_data: [97, 116, 97, 110, 50, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__899: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__899_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__900_value: LeanStringObject<7> =
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
        m_data: [97, 116, 97, 110, 50, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__900: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__900_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__901_value: LeanStringObject<6> =
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
        m_data: [97, 116, 97, 110, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__901: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__901_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__902_value: LeanStringObject<6> =
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
        m_data: [97, 116, 97, 110, 104, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__902: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__902_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__903_value: LeanStringObject<7> =
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
        m_data: [97, 116, 97, 110, 104, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__903: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__903_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__904_value: LeanStringObject<5> =
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
        m_data: [97, 99, 111, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__904: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__904_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__905_value: LeanStringObject<6> =
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
        m_data: [97, 99, 111, 115, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__905: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__905_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__906_value: LeanStringObject<6> =
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
        m_data: [97, 99, 111, 115, 104, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__906: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__906_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__907_value: LeanStringObject<7> =
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
        m_data: [97, 99, 111, 115, 104, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__907: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__907_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__908_value: LeanStringObject<5> =
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
        m_data: [97, 115, 105, 110, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__908: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__908_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__909_value: LeanStringObject<6> =
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
        m_data: [97, 115, 105, 110, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__909: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__909_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__910_value: LeanStringObject<6> =
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
        m_data: [97, 115, 105, 110, 104, 0],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__910: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__910_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__911_value: LeanArrayObject<911> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 911) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 911,
        m_capacity: 911,
        m_data: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__904_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__905_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__906_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__907_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__908_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__909_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__910_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__897_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__898_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__899_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__900_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__901_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__902_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__903_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__890_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__891_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__892_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__893_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__894_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__895_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__896_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__883_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__884_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__885_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__886_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__887_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__888_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__889_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__876_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__877_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__879_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__880_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__881_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__882_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__869_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__870_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__871_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__872_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__873_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__874_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__875_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__862_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__863_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__864_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__865_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__866_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__867_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__868_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__855_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__856_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__857_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__858_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__859_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__860_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__861_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__848_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__849_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__850_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__851_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__852_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__853_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__854_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__841_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__842_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__843_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__844_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__845_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__846_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__847_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__834_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__835_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__836_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__838_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__839_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__840_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__827_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__828_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__829_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__830_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__833_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__820_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__821_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__822_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__823_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__824_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__826_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__813_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__814_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__815_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__816_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__817_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__819_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__806_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__808_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__809_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__810_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__811_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__812_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__802_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__803_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__804_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__805_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__798_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__799_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__800_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__801_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__791_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__792_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__793_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__794_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__795_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__796_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__797_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__784_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__785_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__786_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__787_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__788_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__789_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__790_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__777_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__778_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__779_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__780_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__781_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__782_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__783_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__770_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__771_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__772_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__773_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__774_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__775_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__776_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__763_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__764_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__765_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__766_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__767_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__768_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__769_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__756_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__757_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__758_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__759_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__760_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__761_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__762_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__749_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__750_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__751_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__752_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__753_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__754_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__755_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__745_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__746_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__747_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__748_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__741_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__742_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__743_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__744_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__734_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__735_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__736_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__737_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__738_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__739_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__740_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__727_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__728_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__729_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__730_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__731_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__732_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__733_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__721_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__722_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__723_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__725_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__726_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__713_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__715_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__716_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__717_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__719_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__706_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__707_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__708_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__709_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__710_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__712_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__699_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__698_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__688_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__689_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__690_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__691_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__684_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__685_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__686_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__687_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__677_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__678_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__679_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__680_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__681_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__682_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__683_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__670_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__671_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__672_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__673_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__674_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__675_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__676_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__663_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__664_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__665_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__666_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__667_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__668_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__669_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__656_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__657_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__658_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__659_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__660_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__661_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__662_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__649_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__650_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__651_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__652_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__653_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__654_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__655_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__642_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__643_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__644_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__645_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__646_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__647_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__648_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__635_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__636_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__637_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__638_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__639_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__640_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__641_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__631_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__632_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__633_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__634_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__627_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__628_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__629_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__630_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__620_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__621_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__622_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__623_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__624_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__625_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__626_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__613_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__614_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__615_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__616_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__617_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__618_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__619_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__606_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__607_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__608_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__609_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__610_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__611_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__612_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__599_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__600_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__601_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__602_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__603_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__604_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__605_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__592_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__593_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__594_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__595_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__596_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__597_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__598_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__585_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__586_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__587_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__588_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__589_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__590_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__591_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__578_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__579_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__580_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__581_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__582_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__583_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__584_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__574_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__575_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__576_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__577_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__570_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__571_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__572_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__573_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__563_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__564_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__565_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__566_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__567_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__568_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__569_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__556_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__557_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__558_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__559_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__560_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__561_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__562_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__549_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__550_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__551_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__552_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__553_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__554_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__555_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__542_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__543_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__544_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__545_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__546_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__547_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__548_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__535_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__536_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__537_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__538_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__539_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__540_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__541_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__528_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__529_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__530_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__531_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__532_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__533_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__534_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__521_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__522_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__523_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__524_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__525_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__526_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__527_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__517_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__518_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__519_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__520_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__513_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__514_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__515_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__516_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__506_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__507_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__508_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__509_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__510_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__511_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__512_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__499_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__500_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__501_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__502_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__503_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__504_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__505_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__492_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__493_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__494_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__495_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__496_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__497_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__498_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__485_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__486_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__487_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__488_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__489_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__490_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__491_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__478_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__479_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__481_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__471_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__472_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__473_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__474_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__475_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__476_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__477_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__464_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__465_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__466_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__467_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__468_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__469_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__470_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__460_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__461_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__462_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__463_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__456_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__457_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__458_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__459_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__449_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__450_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__451_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__452_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__453_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__454_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__455_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__442_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__443_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__444_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__445_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__446_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__447_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__448_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__435_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__436_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__437_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__438_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__439_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__440_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__441_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__428_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__429_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__430_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__431_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__432_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__433_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__434_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__421_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__422_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__423_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__424_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__425_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__426_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__427_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__414_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__415_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__416_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__417_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__418_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__419_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__420_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__407_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__408_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__409_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__410_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__411_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__412_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__413_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__403_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__404_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__405_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__406_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__399_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__400_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__401_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__402_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__392_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__393_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__394_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__395_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__396_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__397_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__398_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__385_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__386_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__387_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__388_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__389_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__390_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__391_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__378_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__379_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__380_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__381_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__382_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__383_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__384_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__371_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__372_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__373_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__374_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__375_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__376_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__377_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__364_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__365_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__366_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__367_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__368_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__369_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__358_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__359_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__360_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__361_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__362_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__363_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__350_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__351_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__352_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__353_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__354_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__355_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__356_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__346_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__347_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__348_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__349_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__342_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__343_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__344_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__345_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__335_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__336_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__337_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__338_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__339_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__340_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__341_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__330_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__331_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__332_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__333_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__321_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__322_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__323_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__324_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__325_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__326_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__327_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__314_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__315_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__316_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__318_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__319_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__320_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__307_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__308_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__309_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__310_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__311_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__312_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__313_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__300_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__301_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__303_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__305_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__293_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__294_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__295_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__299_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__290_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__291_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__285_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__288_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__278_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__279_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__281_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__272_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__274_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__276_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__277_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__264_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__265_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__266_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__267_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__268_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__269_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__270_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__257_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__258_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__259_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__246_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__247_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__248_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__249_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__236_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__237_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__238_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__239_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__240_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__241_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__242_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__232_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__233_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__234_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__235_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__228_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__229_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__230_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__231_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__221_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__222_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__223_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__224_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__225_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__226_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__227_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__214_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__215_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__216_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__217_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__218_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__219_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__220_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__207_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__208_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__209_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__210_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__211_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__212_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__213_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__200_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__201_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__202_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__203_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__204_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__205_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__206_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__193_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__194_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__195_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__196_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__197_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__198_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__199_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__186_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__187_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__188_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__189_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__190_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__191_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__192_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__179_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__180_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__181_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__182_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__183_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__184_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__185_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__175_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__176_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__177_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__178_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__171_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__172_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__173_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__174_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__164_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__165_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__166_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__167_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__168_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__169_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__170_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__157_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__158_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__159_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__160_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__161_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__162_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__163_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__150_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__151_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__152_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__153_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__154_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__155_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__156_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__143_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__144_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__145_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__146_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__147_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__148_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__149_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__136_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__137_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__138_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__139_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__140_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__141_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__142_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__129_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__130_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__132_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__133_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__134_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__135_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__122_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__123_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__124_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__125_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__126_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__127_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__128_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__118_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__119_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__120_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__121_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__114_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__115_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__116_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__117_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__107_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__108_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__109_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__110_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__111_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__112_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__113_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__100_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__101_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__102_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__103_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__104_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__105_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__106_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__93_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__94_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__95_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__96_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__97_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__98_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__99_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__86_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__87_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__88_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__89_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__90_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__91_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__92_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__79_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__80_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__81_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__82_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__83_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__84_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__85_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__72_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__73_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__74_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__75_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__76_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__77_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__78_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__65_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__66_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__67_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__68_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__69_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__70_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__71_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__61_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__62_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__63_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__64_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__57_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__58_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__59_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__60_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__50_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__51_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__52_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__53_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__54_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__55_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__56_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__43_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__44_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__45_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__46_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__47_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__48_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__49_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__36_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__37_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__38_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__39_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__40_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__41_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__42_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__29_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__30_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__31_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__32_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__33_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__34_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__35_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__22_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__23_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__24_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__25_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__27_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__28_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__17_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__19_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__20_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__21_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__14_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__911: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__911_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_leanImportsFromRust: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__911_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__0_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 115, 105, 109, 112, 95, 109, 97, 99, 114, 111, 95, 115, 99, 111,
            112, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__1_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 115, 116, 114, 101, 97, 109, 95, 111, 102, 95, 104, 97, 110,
            100, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__2_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115,
            95, 103, 101, 116, 95, 114, 117, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__3_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115,
            95, 109, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__4_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115,
            95, 112, 114, 111, 99, 101, 115, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__5_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 115, 101, 116, 95, 114, 101, 100, 117, 99, 105, 98, 105, 108,
            105, 116, 121, 95, 115, 116, 97, 116, 117, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__6_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 109, 97, 105, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__7_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115,
            95, 103, 101, 116, 95, 110, 117, 109, 95, 116, 104, 114, 101, 97, 100, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__8_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115,
            95, 103, 101, 116, 95, 112, 114, 111, 102, 105, 108, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__9_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 114, 101, 99, 117, 114, 115, 111, 114, 95, 107, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__10_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 95,
            104, 105, 110, 116, 115, 95, 103, 101, 116, 95, 104, 101, 105, 103, 104, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__11_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 114, 101, 103, 105, 115, 116, 101, 114, 95, 111, 112, 116, 105,
            111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__12_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 112, 114, 105, 118, 97, 116, 101, 95, 116, 111, 95, 117, 115,
            101, 114, 95, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__13_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 95, 105, 110,
            102, 111, 95, 102, 114, 111, 109, 95, 99, 108, 97, 115, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__14_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 113, 117, 111, 116, 95, 118, 97, 108, 95, 107, 105, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__15_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 114, 101, 99, 117, 114, 115, 111, 114, 95, 105, 115, 95, 117,
            110, 115, 97, 102, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__16_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 111, 112, 116, 105, 111, 110, 115, 95, 117, 112, 100, 97, 116,
            101, 95, 98, 111, 111, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__17_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 112, 114, 105, 118, 97, 116, 101, 95, 112, 114, 101, 102, 105,
            120, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__18_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 97, 112, 112, 101, 110, 100, 95, 105,
            110, 100, 101, 120, 95, 97, 102, 116, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__19_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 104, 97, 115, 104, 95, 101, 120, 112,
            111, 114, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__20_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 109, 107, 95, 110, 117, 109, 101, 114,
            97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__21_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 109, 107, 95, 115, 116, 114, 105, 110,
            103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__22_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 111, 112, 97, 113, 117, 101, 95, 118, 97, 108, 95, 105, 115, 95,
            117, 110, 115, 97, 102, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__23_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 111, 112, 116, 105, 111, 110, 115, 95, 103, 101, 116, 95, 98,
            111, 111, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__24_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 111, 112, 116, 105, 111, 110, 115, 95, 103, 101, 116, 95, 101,
            109, 112, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__25_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 115, 121, 110, 116, 97, 120, 95, 105, 100, 101,
            110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__26_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 116, 104, 101, 111, 114, 101, 109, 95, 118, 97,
            108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__26_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__27_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 97, 112, 112, 101, 110, 100, 95, 97, 102,
            116, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__28_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 97, 112, 112, 101, 110, 100, 95, 98, 101,
            102, 111, 114, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__29_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110,
            95, 105, 110, 102, 111, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__30_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 113, 117, 111, 116, 95, 118, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__30_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__31_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 114, 101, 99, 117, 114, 115, 111, 114, 95, 118,
            97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__32_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 114, 101, 100, 117, 99, 105, 98, 105, 108, 105,
            116, 121, 95, 104, 105, 110, 116, 115, 95, 114, 101, 103, 117, 108, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__32_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__33_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 108, 111, 99, 97, 108, 95, 100, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__34_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 109, 97, 110, 103, 108, 101, 100, 95, 98, 111,
            120, 101, 100, 95, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__34_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__35_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 111, 112, 97, 113, 117, 101, 95, 118, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__35_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__36_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 111, 117, 116, 112, 97, 114, 97, 109, 95, 97, 114,
            103, 115, 95, 105, 109, 112, 108, 105, 99, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__37_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 117,
            110, 115, 97, 116, 105, 115, 102, 105, 101, 100, 95, 99, 111, 110, 115, 116, 114, 97,
            105, 110, 116, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__37_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__38_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 117,
            110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 95, 111, 112, 101, 114, 97, 116, 105,
            111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__39_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 117, 115, 101, 114, 95, 101, 114,
            114, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__39_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__40_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 108, 101, 116, 95, 100, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__40_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__41_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 114,
            101, 115, 111, 117, 114, 99, 101, 95, 101, 120, 104, 97, 117, 115, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__41_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__42_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 114,
            101, 115, 111, 117, 114, 99, 101, 95, 101, 120, 104, 97, 117, 115, 116, 101, 100, 95,
            102, 105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__42_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__43_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 114,
            101, 115, 111, 117, 114, 99, 101, 95, 118, 97, 110, 105, 115, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__43_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__44_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 116,
            105, 109, 101, 95, 101, 120, 112, 105, 114, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__44_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__45_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 112,
            101, 114, 109, 105, 115, 115, 105, 111, 110, 95, 100, 101, 110, 105, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__45_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__46_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 112,
            101, 114, 109, 105, 115, 115, 105, 111, 110, 95, 100, 101, 110, 105, 101, 100, 95, 102,
            105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__46_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__47_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 112,
            114, 111, 116, 111, 99, 111, 108, 95, 101, 114, 114, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__47_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__48_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 114,
            101, 115, 111, 117, 114, 99, 101, 95, 98, 117, 115, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__48_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__49_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105,
            110, 116, 101, 114, 114, 117, 112, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__49_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__50_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105,
            110, 118, 97, 108, 105, 100, 95, 97, 114, 103, 117, 109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__50_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__51_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105,
            110, 118, 97, 108, 105, 100, 95, 97, 114, 103, 117, 109, 101, 110, 116, 95, 102, 105,
            108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__51_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__52_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 110,
            111, 95, 102, 105, 108, 101, 95, 111, 114, 95, 100, 105, 114, 101, 99, 116, 111, 114,
            121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__52_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__53_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 110,
            111, 95, 115, 117, 99, 104, 95, 116, 104, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__53_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__54_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 110,
            111, 95, 115, 117, 99, 104, 95, 116, 104, 105, 110, 103, 95, 102, 105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__54_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__55_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 111,
            116, 104, 101, 114, 95, 101, 114, 114, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__55_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__56_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 104,
            97, 114, 100, 119, 97, 114, 101, 95, 102, 97, 117, 108, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__56_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__57_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105,
            108, 108, 101, 103, 97, 108, 95, 111, 112, 101, 114, 97, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__57_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__58_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105,
            110, 97, 112, 112, 114, 111, 112, 114, 105, 97, 116, 101, 95, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__58_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__59_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105,
            110, 97, 112, 112, 114, 111, 112, 114, 105, 97, 116, 101, 95, 116, 121, 112, 101, 95,
            102, 105, 108, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__59_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__60_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95,
            118, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__60_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__61_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 97,
            108, 114, 101, 97, 100, 121, 95, 101, 120, 105, 115, 116, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__61_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__62_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 97,
            108, 114, 101, 97, 100, 121, 95, 101, 120, 105, 115, 116, 115, 95, 102, 105, 108, 101,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__62_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__63_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 101,
            111, 102, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__63_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__64_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 97, 120, 105, 111, 109, 95, 118, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__64_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__65_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 98, 111, 111, 108, 95, 100, 97, 116, 97, 95, 118,
            97, 108, 117, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__65: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__65_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__66_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
            114, 95, 118, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__66: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__66_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__67_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
            95, 118, 97, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__67: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__67_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__68_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 101, 110, 118, 105,
            114, 111, 110, 109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__68: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__68_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__69_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 108, 111, 99, 97,
            108, 95, 99, 116, 120, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__69: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__69_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__70_value: LeanStringObject<23> =
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
            108, 101, 97, 110, 95, 109, 107, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95,
            100, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__70: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__70_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__71_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 110, 117, 109, 95,
            105, 110, 100, 105, 99, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__71: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__71_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__72_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 100, 101, 99, 108, 95, 98, 105, 110,
            100, 101, 114, 95, 105, 110, 102, 111, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__72: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__72_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__73_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 102, 105, 110, 100,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__73: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__73_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__74_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 105, 115, 95, 101,
            109, 112, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__74: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__74_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__75_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 109, 107, 95, 108,
            101, 116, 95, 100, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__75: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__75_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__76_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 109, 107, 95, 108,
            111, 99, 97, 108, 95, 100, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__76: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__76_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__77_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 109, 107, 95, 115, 117, 99, 99, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__77: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__77_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__78_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 109, 107, 95, 122, 101, 114, 111, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__78: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__78_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__79_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 108, 105, 115, 116, 95, 116, 111, 95, 97, 114, 114, 97, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__79: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__79_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__80_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 108, 105, 116, 95, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__80: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__80_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__81_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 108, 111, 97, 100, 95, 100, 121, 110, 108, 105, 98, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__81: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__81_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__82_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 108, 111, 97, 100, 95, 112, 108, 117, 103, 105, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__82: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__82_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__83_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 101, 114, 97, 115,
            101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__83: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__83_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__84_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 109, 107, 95, 105, 109, 97, 120, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__84: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__84_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__85_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 109, 107, 95, 109, 97, 120, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__85: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__85_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__86_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 109, 107, 95, 109, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__86: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__86_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__87_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 109, 107, 95, 112, 97, 114, 97,
            109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__87: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__87_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__88_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 100, 101, 112, 116, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__88: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__88_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__89_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 104, 97, 115, 95, 109, 118, 97,
            114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__89: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__89_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__90_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 104, 97, 115, 95, 112, 97, 114, 97,
            109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__90: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__90_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__91_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 104, 97, 115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__91: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__91_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__92_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 100, 105, 97, 103, 95, 105,
            115, 95, 101, 110, 97, 98, 108, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__92: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__92_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__93_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 103, 101, 116, 95, 100, 105,
            97, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__93: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__93_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__94_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 114, 101, 99, 111, 114, 100,
            95, 117, 110, 102, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__94: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__94_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__95_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 115, 101, 116, 95, 100, 105,
            97, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__95: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__95_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__96_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 112, 114, 105, 118, 97, 116, 101, 95, 110, 97,
            109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__96: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__96_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__97_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 116, 114, 97, 99, 101, 95, 99, 108, 97, 115, 115,
            95, 101, 110, 97, 98, 108, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__97: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__97_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__98_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 105, 115, 95, 117, 110, 115, 97, 102, 101, 95, 105, 110, 100,
            117, 99, 116, 105, 118, 101, 95, 100, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__98: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__98_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__99_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 105, 115, 95, 105, 110, 97, 99, 99, 101, 115, 115, 105, 98, 108,
            101, 95, 117, 115, 101, 114, 95, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__99: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__99_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__100_value: LeanStringObject<16> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 109, 97, 116, 99, 104, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__100: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__100_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__101_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 111, 117, 116, 95, 112, 97, 114, 97, 109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__101: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__101_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__102_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 105, 114, 95, 102, 111, 114, 109, 97, 116, 95, 102, 110, 95, 98,
            111, 100, 121, 95, 104, 101, 97, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__102: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__102_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__103_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__103: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__103_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__104_value: LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 105, 115, 95, 99, 108, 97, 115, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__104: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__104_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__105_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 101, 112, 114, 105, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__105: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__105_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__106_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 101, 112, 114, 105, 110, 116, 108, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__106: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__106_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__107_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 116, 111, 95, 115,
            116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__107: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__107_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__108_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 105, 114, 95, 101, 109, 105, 116, 95, 108, 108, 118, 109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__108: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__108_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__109_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 114, 95, 102, 105, 110, 100, 95, 101, 110, 118, 95, 100,
            101, 99, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__109: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__109_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__110_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 105, 114, 95, 102, 105, 110, 100, 95, 101, 110, 118, 95, 100,
            101, 99, 108, 95, 98, 111, 120, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__110: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__110_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__111_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 118, 97, 108,
            95, 105, 115, 95, 117, 110, 115, 97, 102, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__111: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__111_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__112_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 105, 110, 105, 116, 95, 115, 101, 97, 114, 99, 104, 95, 112, 97,
            116, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__112: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__112_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__113_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 105, 111, 95, 99, 97, 110, 99, 101, 108, 95, 116, 111, 107, 101,
            110, 95, 105, 115, 95, 115, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__113: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__113_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__114_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 104, 97, 115, 95, 111, 117, 116, 95, 112, 97, 114, 97, 109, 115,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__114: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__114_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__115_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 118, 97, 108,
            95, 105, 115, 95, 114, 101, 99, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__115: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__115_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__116_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 118, 97, 108,
            95, 105, 115, 95, 114, 101, 102, 108, 101, 120, 105, 118, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__116: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__116_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__117_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 104, 97, 115, 95, 109, 97, 116, 99, 104, 95, 112, 97, 116, 116,
            101, 114, 110, 95, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__117: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__117_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__118_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 114, 101, 100, 117, 99, 105, 98, 105, 108,
            105, 116, 121, 95, 115, 116, 97, 116, 117, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__118: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__118_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__119_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 103, 101, 116, 95, 114, 101, 103, 117, 108, 97, 114, 95, 105,
            110, 105, 116, 95, 102, 110, 95, 110, 97, 109, 101, 95, 102, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__119: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__119_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__120_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 121, 109, 98, 111, 108, 95, 115, 116,
            101, 109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__120: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__120_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__121_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 103, 101, 116, 95, 108, 109, 118, 97, 114, 95, 97, 115, 115,
            105, 103, 110, 109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__121: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__121_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__122_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 109, 118, 97, 114, 95, 97, 115, 115, 105,
            103, 110, 109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__122: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__122_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__123_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 111, 112, 116, 105, 111, 110, 95, 100, 101,
            99, 108, 115, 95, 97, 114, 114, 97, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__123: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__123_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__124_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 112, 114, 111, 102, 105, 108, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__124: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__124_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__125_value: LeanStringObject<28> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 112, 114, 111, 102, 105, 108, 101, 114, 95,
            116, 104, 114, 101, 115, 104, 111, 108, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__125: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__125_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__126_value: LeanStringObject<33> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 100, 101, 108, 97, 121, 101, 100, 95, 109,
            118, 97, 114, 95, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__126: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__126_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__127_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 103, 101, 116, 95, 101, 120, 112, 111, 114, 116, 95, 110, 97,
            109, 101, 95, 102, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__127: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__127_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__128_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 103, 101, 116, 95, 105, 110, 105, 116, 95, 102, 110, 95, 110,
            97, 109, 101, 95, 102, 111, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__128: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__128_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__129_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 115, 111, 114, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__129: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__129_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__130_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 111, 102, 95, 110, 97, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__130: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__130_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__131_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 111, 102, 95, 110, 97, 116,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__131: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__131_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__132_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 108, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__132: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__132_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__133_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 109, 100, 97, 116, 97, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__133: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__133_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__134_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 109, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__134: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__134_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__135_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 112, 114, 111, 106, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__135: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__135_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__136_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 102, 111, 114, 97, 108,
            108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__136: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__136_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__137_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 102, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__137: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__137_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__138_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 108, 97, 109, 98, 100, 97,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__138: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__138_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__139_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 108, 101, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__139: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__139_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__140_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 108, 111, 111, 115, 101, 95, 98, 118,
            97, 114, 95, 114, 97, 110, 103, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__140: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__140_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__141_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 97, 112, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__141: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__141_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__142_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 98, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__142: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__142_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__143_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 99, 111, 110, 115, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__143: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__143_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__144_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 108, 101, 118, 101,
            108, 95, 112, 97, 114, 97, 109, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__144: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__144_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__145_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 109, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__145: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__145_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__146_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 104, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__146: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__146_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__147_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 115, 95, 104, 97, 118, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__147: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__147_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__148_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 98, 105, 110, 100, 101, 114, 95, 105,
            110, 102, 111, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__148: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__148_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__149_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 99, 111, 110, 115, 117, 109, 101, 95,
            116, 121, 112, 101, 95, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__149: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__149_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__150_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 101, 120, 112, 114,
            95, 109, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__150: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__150_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__151_value: LeanStringObject<19> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 102, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__151: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__151_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__152_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 108, 101, 118, 101,
            108, 95, 109, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__152: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__152_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__153_value: LeanStringObject<30> =
    LeanStringObject {
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
            108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 102,
            114, 101, 101, 95, 114, 101, 103, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__153: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__153_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__154_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 109,
            97, 114, 107, 95, 113, 117, 111, 116, 95, 105, 110, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__154: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__154_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__155_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 113,
            117, 111, 116, 95, 105, 110, 105, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__155: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__155_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__156_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 101, 114, 97, 115, 101, 95, 109, 97, 99, 114, 111, 95, 115, 99,
            111, 112, 101, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__156: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__156_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__157_value: LeanStringObject<51> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 51,
        m_capacity: 51,
        m_length: 50,
        m_data: [
            108, 101, 97, 110, 95, 101, 108, 97, 98, 95, 101, 110, 118, 105, 114, 111, 110, 109,
            101, 110, 116, 95, 117, 112, 100, 97, 116, 101, 95, 98, 97, 115, 101, 95, 97, 102, 116,
            101, 114, 95, 107, 101, 114, 110, 101, 108, 95, 97, 100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__157: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__157_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__158_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            108, 101, 97, 110, 95, 101, 110, 97, 98, 108, 101, 95, 105, 110, 105, 116, 105, 97,
            108, 105, 122, 101, 114, 95, 101, 120, 101, 99, 117, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__158: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__158_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__159_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 97,
            100, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__159: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__159_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__160_value: LeanStringObject<22> =
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
            108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 102,
            105, 110, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__160: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__160_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__161_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 95, 118, 97,
            108, 95, 103, 101, 116, 95, 115, 97, 102, 101, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__161: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__161_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__162_value: LeanStringObject<35> =
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
            108, 101, 97, 110, 95, 100, 101, 108, 97, 121, 101, 100, 95, 109, 118, 97, 114, 95, 97,
            115, 115, 105, 103, 110, 109, 101, 110, 116, 95, 102, 118, 97, 114, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__162: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__162_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__163_value: LeanStringObject<45> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 45,
        m_capacity: 45,
        m_length: 44,
        m_data: [
            108, 101, 97, 110, 95, 100, 101, 108, 97, 121, 101, 100, 95, 109, 118, 97, 114, 95, 97,
            115, 115, 105, 103, 110, 109, 101, 110, 116, 95, 109, 118, 97, 114, 95, 105, 100, 95,
            112, 101, 110, 100, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__163: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__163_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__164_value: LeanStringObject<27> =
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
            108, 101, 97, 110, 95, 100, 101, 109, 97, 110, 103, 108, 101, 95, 98, 116, 95, 108,
            105, 110, 101, 95, 99, 115, 116, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__164: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__164_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__165_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 101, 108, 97, 98, 95, 101, 110, 118, 105, 114, 111, 110, 109,
            101, 110, 116, 95, 111, 102, 95, 107, 101, 114, 110, 101, 108, 95, 101, 110, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__165: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__165_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__166_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            108, 101, 97, 110, 95, 101, 108, 97, 98, 95, 101, 110, 118, 105, 114, 111, 110, 109,
            101, 110, 116, 95, 116, 111, 95, 107, 101, 114, 110, 101, 108, 95, 101, 110, 118, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__166: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__166_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__167_value: LeanStringObject<20> =
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
            108, 101, 97, 110, 95, 100, 97, 116, 97, 95, 118, 97, 108, 117, 101, 95, 98, 101, 113,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__167: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__167_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__168_value: LeanStringObject<21> =
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
            108, 101, 97, 110, 95, 100, 97, 116, 97, 95, 118, 97, 108, 117, 101, 95, 98, 111, 111,
            108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__168: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__168_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__169_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 95, 100, 97, 116, 97, 95, 118, 97, 108, 117, 101, 95, 116, 111, 95,
            115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__169: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__169_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__170_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 100, 101, 99, 108, 95, 103, 101, 116, 95, 115, 111, 114, 114,
            121, 95, 100, 101, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__170: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__170_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__171_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            108, 101, 97, 110, 95, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 95, 118,
            97, 108, 95, 105, 115, 95, 117, 110, 115, 97, 102, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__171: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__171_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__172_value: LeanStringObject<15> =
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
            108, 101, 97, 110, 95, 97, 100, 100, 95, 97, 108, 105, 97, 115, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__172: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__172_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__173_value: LeanStringObject<24> =
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
            108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 116, 111, 95, 108, 105, 115, 116, 95,
            105, 109, 112, 108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__173: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__173_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__174_value: LeanStringObject<18> =
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
            108, 101, 97, 110, 95, 97, 115, 115, 105, 103, 110, 95, 108, 109, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__174: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__174_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__175_value: LeanStringObject<17> =
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
            108, 101, 97, 110, 95, 97, 115, 115, 105, 103, 110, 95, 109, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__175: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__175_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__176_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            108, 101, 97, 110, 95, 97, 116, 116, 114, 105, 98, 117, 116, 101, 95, 97, 112, 112,
            108, 105, 99, 97, 116, 105, 111, 110, 95, 116, 105, 109, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__176: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__176_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__177_value: LeanStringObject<25> =
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
            108, 101, 97, 110, 95, 97, 120, 105, 111, 109, 95, 118, 97, 108, 95, 105, 115, 95, 117,
            110, 115, 97, 102, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__177: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__177_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__178_value: LeanArrayObject<245> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 245) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 245,
        m_capacity: 245,
        m_data: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__172_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__173_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__174_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__175_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__176_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__177_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__171_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__167_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__168_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__169_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__170_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__161_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__162_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__163_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__164_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__165_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__166_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__157_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__158_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__159_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__160_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__153_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__154_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__155_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__156_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__148_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__149_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__150_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__151_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__152_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__144_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__145_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__146_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__147_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__140_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__141_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__142_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__143_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__136_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__137_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__138_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__139_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__132_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__133_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__134_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__135_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__129_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__130_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__131_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__126_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__127_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__128_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__121_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__122_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__123_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__124_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__125_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__118_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__119_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__120_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__117_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__114_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__115_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__116_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__111_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__112_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__113_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__105_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__106_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__107_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__108_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__109_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__110_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__102_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__103_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__104_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__99_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__100_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__101_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__96_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__97_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__98_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__92_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__93_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__94_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__95_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__88_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__89_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__90_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__91_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__84_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__85_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__86_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__87_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__77_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__78_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__79_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__80_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__81_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__82_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__83_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__73_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__74_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__75_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__76_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__71_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__72_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__64_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__65_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__66_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__67_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__68_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__69_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__70_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__60_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__61_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__62_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__63_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__56_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__57_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__58_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__59_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__49_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__50_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__51_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__52_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__53_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__54_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__55_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__45_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__46_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__47_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__48_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__41_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__42_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__43_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__44_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__37_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__38_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__39_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__40_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__33_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__34_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__35_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__36_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__29_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__30_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__31_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__32_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__25_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__26_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__27_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__28_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__19_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__20_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__21_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__22_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__23_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__24_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__17_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__14_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__178: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__178_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__178_value)
        as *mut LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(builtin);
}
