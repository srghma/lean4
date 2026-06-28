// Lean compiler output
// Module: Lean.Compiler.LCNF.EmitRust.LeanhGenerated
// Imports: Init Init Init.Prelude
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
use crate::r#gen::Init::{initialize_Init, runtime_initialize_Init};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__5_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__6_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__7_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__9_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__10_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__11_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__12_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__13_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__14_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__15_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__16_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 108, 118, 109, 95, 105, 115, 95, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__17_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__18_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__19_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__20_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__21_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__22_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 109, 105,
        110, 111, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__23_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 112, 97,
        116, 99, 104, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__24_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 115, 112,
        101, 99, 105, 97, 108, 95, 100, 101, 115, 99, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__25_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__27_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 119, 105, 110, 100, 111, 119, 115, 95, 103, 101, 116, 95, 110, 101,
        120, 116, 95, 116, 114, 97, 110, 115, 105, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__28_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__29_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 109, 117, 108,
        116, 105, 99, 97, 115, 116, 95, 108, 111, 111, 112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__30_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 109, 117, 108,
        116, 105, 99, 97, 115, 116, 95, 116, 116, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__31_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 116, 116, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__32_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 119, 97, 105, 116, 95, 114, 101,
        97, 100, 97, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__33_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__34_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 105, 115,
        95, 114, 101, 108, 101, 97, 115, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__35_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 118, 101, 114, 115, 105, 111, 110, 95, 103, 101, 116, 95, 109, 97,
        106, 111, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__36_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 103, 101, 116, 115, 111, 99, 107,
        110, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__37_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__38_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__39_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__40_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 98, 114, 111,
        97, 100, 99, 97, 115, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__41_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 109, 101, 109,
        98, 101, 114, 115, 104, 105, 112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__42_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 115, 101, 116, 95, 109, 117, 108,
        116, 105, 99, 97, 115, 116, 95, 105, 110, 116, 101, 114, 102, 97, 99, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__43_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__44_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 105, 109, 101, 114, 95, 114, 101, 115, 101, 116,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__45_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__46_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__46_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__47_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 99, 97, 110, 99, 101, 108, 95, 114,
        101, 99, 118, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__48_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 99, 111, 110, 110, 101, 99, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__49_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 117, 100, 112, 95, 103, 101, 116, 112, 101, 101, 114,
        110, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__50_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__50_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__51_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__51_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__52_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 115, 104, 117, 116, 100, 111, 119,
        110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__53_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 116, 114, 121, 95, 97, 99, 99, 101,
        112, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__54_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 119, 97, 105, 116, 95, 114, 101, 97,
        100, 97, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__55_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__56_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__57_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 107, 101, 101, 112, 97, 108, 105,
        118, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__57_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__58_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__58_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__59_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__59: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__60_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 110, 111, 100, 101, 108, 97, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__60: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__60_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__61_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 99, 97, 110, 99, 101, 108, 95, 114,
        101, 99, 118, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__61: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__61_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__62_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 99, 111, 110, 110, 101, 99, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__62: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__62_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__63_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 103, 101, 116, 112, 101, 101, 114,
        110, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__63: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__64_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 103, 101, 116, 115, 111, 99, 107,
        110, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__65_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 115, 105, 103, 110, 97, 108, 95, 99, 97, 110, 99, 101,
        108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__65: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__65_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__66_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__66: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__66_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__67_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 115, 105, 103, 110, 97, 108, 95, 110, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__67: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__67_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__68_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 115, 105, 103, 110, 97, 108, 95, 115, 116, 111, 112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__68: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__68_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__69_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__69: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__69_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__70_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__70: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__70_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__71_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 116, 99, 112, 95, 99, 97, 110, 99, 101, 108, 95, 97,
        99, 99, 101, 112, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__71: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__71_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__72_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__72: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__72_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__73_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__73: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__73_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__74_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 117, 110, 115, 101, 116, 101, 110, 118,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__74: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__74_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__75_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__75: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__75_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__76_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__76: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__76_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__77_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__77: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__77_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__78_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 115, 101, 116, 95, 112, 114, 111, 99, 101, 115, 115,
        95, 116, 105, 116, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__78: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__78_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__79_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 104, 111, 115, 116, 110,
        97, 109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__79: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__79_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__80_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__80: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__80_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__81_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__81: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__81_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__82_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 112, 114, 105, 111, 114,
        105, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__82: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__82_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__83_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__83: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__83_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__84_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__84: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__84_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__85_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 115, 101, 116, 112, 114, 105, 111, 114,
        105, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__85: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__85_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__86_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__86: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__86_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__87_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__87: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__87_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__88_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__88: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__88_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__89_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__89: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__89_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__90_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 95, 103, 114, 111, 117,
        112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__90: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__90_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__91_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 111, 115, 95, 103, 101, 116, 95, 112, 97, 115, 115,
        119, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__91: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__91_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__92_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__92: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__92_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__93_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 97, 118, 97, 105, 108, 97, 98, 108,
        101, 95, 109, 101, 109, 111, 114, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__93: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__93_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__94_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 99, 111, 110, 115, 116, 114, 97,
        105, 110, 101, 100, 95, 109, 101, 109, 111, 114, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__94: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__94_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__95_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 102, 114, 101, 101, 95, 109, 101,
        109, 111, 114, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__95: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__95_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__96_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 112, 114, 111, 99, 101, 115, 115,
        95, 116, 105, 116, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__96: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__96_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__97_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 103, 101, 116, 95, 116, 111, 116, 97, 108, 95, 109,
        101, 109, 111, 114, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__97: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__97_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__98_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__98: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__98_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__99_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__99: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__99_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__100_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__100: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__100_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__101_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__101: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__101_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__102_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 100, 110, 115, 95, 103, 101, 116, 95, 105, 110, 102,
        111, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__102: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__102_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__103_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 100, 110, 115, 95, 103, 101, 116, 95, 110, 97, 109,
        101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__103: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__103_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__104_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 101, 118, 101, 110, 116, 95, 108, 111, 111, 112, 95,
        97, 108, 105, 118, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__104: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__104_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__105_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 117, 118, 95, 101, 118, 101, 110, 116, 95, 108, 111, 111, 112, 95,
        99, 111, 110, 102, 105, 103, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__105: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__105_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__106_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__106: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__106_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__107_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__107: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__107_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__108_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 117, 105, 110, 116, 49,
        54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__108: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__108_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__109_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 117, 105, 110, 116, 51,
        50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__109: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__109_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__110_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 117, 105, 110, 116, 54,
        52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__110: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__110_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__111_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 117, 105, 110, 116, 56, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__111: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__111_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__112_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__112: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__112_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__113_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__113: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__113_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__114_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 115, 104, 105, 102, 116, 95, 114, 105,
        103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__114: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__114_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__115_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__115: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__115_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__116_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 102, 108, 111, 97, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__116: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__116_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__117_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 116, 111, 95, 102, 108, 111, 97, 116,
        51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__117: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__117_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__118_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__118: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__118_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__119_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__119: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__119_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__120_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 111, 102, 95, 110, 97, 116, 95, 109,
        107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__120: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__120_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__121_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 115, 104, 105, 102, 116, 95, 108, 101,
        102, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__121: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__121_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__122_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__122: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__122_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__123_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__123: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__123_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__124_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__124: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__124_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__125_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__125: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__125_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__126_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__126: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__126_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__127_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__127: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__127_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__128_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__128: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__128_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__129_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 117, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__129: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__129_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__130_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__130: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__130_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 117, 112, 100, 97, 116, 101, 95, 101, 110, 118, 95, 97, 116, 116,
        114, 105, 98, 117, 116, 101, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__132_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__132: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__132_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__133_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 115, 105, 122, 101, 95, 99, 111, 109, 112, 108, 101, 109, 101,
        110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__133: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__133_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__134_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__134: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__134_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__135_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__135: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__135_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__136_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__136: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__136_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__137_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 102, 108, 111, 97, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__137: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__137_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__138_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 102, 108, 111, 97, 116,
        51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__138: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__138_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__139_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__139: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__139_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__140_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 117, 105, 110, 116, 49,
        54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__140: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__140_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__141_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 117, 105, 110, 116, 51,
        50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__141: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__141_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__142_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 116, 111, 95, 117, 105, 110, 116, 54,
        52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__142: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__142_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__143_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__143: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__143_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__144_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__144: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__144_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__145_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__145: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__145_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__146_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__146: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__146_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__147_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__147: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__147_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__148_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 115, 104, 105, 102, 116, 95, 108, 101,
        102, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__148: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__148_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__149_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 115, 104, 105, 102, 116, 95, 114, 105,
        103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__149: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__149_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__150_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__150: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__150_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__151_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__151: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__151_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__152_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__152: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__152_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__153_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__153: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__153_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__154_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__154: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__154_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__155_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__155: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__155_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__156_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__156: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__156_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__157_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 117, 105, 110, 116,
        49, 54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__157: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__157_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__158_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 117, 105, 110, 116,
        51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__158: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__158_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__159_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 117, 105, 110, 116,
        56, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__159: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__159_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__160_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 116, 111, 95, 117, 115, 105, 122,
        101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__160: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__160_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__161_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__161: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__161_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__162_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__162: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__162_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__163_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 56, 95, 99, 111, 109, 112, 108, 101, 109, 101,
        110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__163: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__163_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__164_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 111, 102, 95, 110, 97, 116, 95, 109,
        107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__164: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__164_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__165_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 115, 104, 105, 102, 116, 95, 108,
        101, 102, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__165: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__165_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__166_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 115, 104, 105, 102, 116, 95, 114,
        105, 103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__166: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__166_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__167_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__167: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__167_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__168_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__168: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__168_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__169_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__169: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__169_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__170_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__170: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__170_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__171_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__171: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__171_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__172_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__172: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__172_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__173_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__173: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__173_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__174_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__174: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__174_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__175_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__175: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__175_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__176_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__176: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__176_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__177_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__177: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__177_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__178_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__178: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__178_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__179_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__179: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__179_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__180_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__180: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__180_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__181_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 54, 52, 95, 99, 111, 109, 112, 108, 101, 109,
        101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__181: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__181_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__182_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__182: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__182_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__183_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__183: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__183_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__184_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__184: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__184_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__185_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__185: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__185_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__186_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__186: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__186_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__187_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__187: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__187_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__188_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__188: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__188_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__189_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110, 116,
        49, 54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__189: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__189_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__190_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110, 116,
        54, 52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__190: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__190_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__191_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 117, 105, 110, 116,
        56, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__191: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__191_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__192_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 116, 111, 95, 117, 115, 105, 122,
        101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__192: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__192_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__193_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__193: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__193_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__194_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__194: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__194_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__195_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__195: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__195_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__196_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 111, 102, 95, 110, 97, 116, 95, 109,
        107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__196: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__196_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__197_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 115, 104, 105, 102, 116, 95, 108,
        101, 102, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__197: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__197_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__198_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 115, 104, 105, 102, 116, 95, 114,
        105, 103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__198: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__198_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__199_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__199: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__199_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__200_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__200: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__200_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__201_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__201: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__201_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__202_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__202: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__202_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__203_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__203: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__203_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__204_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__204: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__204_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__205_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__205: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__205_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__206_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__206: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__206_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__207_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 117, 105, 110, 116,
        54, 52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__207: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__207_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__208_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 117, 105, 110, 116,
        56, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__208: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__208_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__209_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 117, 115, 105, 122,
        101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__209: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__209_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__210_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__210: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__210_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__211_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__211: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__211_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__212_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 51, 50, 95, 99, 111, 109, 112, 108, 101, 109,
        101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__212: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__212_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__213_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__213: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__213_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__214_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 115, 104, 105, 102, 116, 95, 108,
        101, 102, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__214: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__214_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__215_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 115, 104, 105, 102, 116, 95, 114,
        105, 103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__215: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__215_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__216_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__216: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__216_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__217_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__217: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__217_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__218_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__218: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__218_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__219_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__219: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__219_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__220_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 116, 111, 95, 117, 105, 110, 116,
        51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__220: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__220_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__221_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__221: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__221_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__222_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__222: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__222_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__223_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__223: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__223_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__224_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__224: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__224_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__225_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__225: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__225_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__226_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__226: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__226_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__227_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 111, 102, 95, 110, 97, 116, 95, 109,
        107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__227: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__227_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__228_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__228: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__228_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__229_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__229: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__229_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__230_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__230: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__230_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__231_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__231: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__231_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__232_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__232: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__232_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__233_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__233: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__233_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__234_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 117, 105, 110, 116, 49, 54, 95, 99, 111, 109, 112, 108, 101, 109,
        101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__234: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__234_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__235_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__235: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__235_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__236_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111, 114,
        109, 95, 119, 105, 110, 100, 111, 119, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__236: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__236_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__237_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__237: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__237_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__238_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__238: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__238_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__239_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__239: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__239_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__240_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__240: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__240_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__241_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__241: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__241_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__242_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__242: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__242_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        108, 101, 97, 110, 95, 115, 121, 110, 116, 104, 95, 112, 101, 110, 100, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__246_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111, 114,
        109, 95, 101, 109, 115, 99, 114, 105, 112, 116, 101, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__246: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__246_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__247_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111, 114,
        109, 95, 110, 98, 105, 116, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__247: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__247_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__248_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111, 114,
        109, 95, 111, 115, 120, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__248: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__248_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__249_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 115, 121, 115, 116, 101, 109, 95, 112, 108, 97, 116, 102, 111, 114,
        109, 95, 116, 97, 114, 103, 101, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__249: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__249_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 102, 114, 111, 110,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 105, 115, 101, 109,
        112, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 112, 114, 101, 118,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 116, 97, 107, 101,
        119, 104, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 116, 111, 115, 116,
        114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__257_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 112, 114,
        101, 118, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__257: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__257_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__258_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 115, 101,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__258: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__258_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__259_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 118, 97, 108, 105, 100, 97, 116,
        101, 95, 117, 116, 102, 56, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__259: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__259_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 100, 114, 111, 112,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 115, 117, 98, 115, 116, 114, 105, 110, 103, 95, 101, 120, 116, 114,
        97, 99, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__264_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 101, 120,
        116, 114, 97, 99, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__264: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__264_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__265_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 103, 101,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__265: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__265_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__266_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 103, 101,
        116, 95, 98, 97, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__266: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__266_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__267_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 103, 101,
        116, 95, 102, 97, 115, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__267: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__267_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__268_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 103, 101,
        116, 95, 111, 112, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__268: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__268_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__269_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 110, 101,
        120, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__269: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__269_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__270_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 110, 101,
        120, 116, 95, 102, 97, 115, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__270: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__270_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__272_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__272: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__272_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__274_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 116, 111, 95, 117, 116, 102, 56, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__274: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__274_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__276_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 97, 116,
        95, 101, 110, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__276: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__276_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__277_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 117, 116, 102, 56, 95, 98, 121,
        116, 101, 95, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__277: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__277_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__278_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__278: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__278_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__279_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__279: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__279_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 110, 101, 120, 116, 119, 104, 105,
        108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__281_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 111, 102, 95, 117, 115, 105, 122,
        101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__281: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__281_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 111, 102, 102, 115, 101, 116, 111,
        102, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 112, 111, 115, 95, 109, 105, 110,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 112, 111, 115, 95, 115, 117, 98, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__285_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 105, 115, 95, 118, 97, 108, 105,
        100, 95, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__285: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__285_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 105, 115, 101, 109, 112, 116, 121,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 105, 115, 112, 114, 101, 102, 105,
        120, 111, 102, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__288_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 108, 101, 110, 103, 116, 104, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__288: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__288_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__290_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 103, 101, 116, 95, 98, 121, 116,
        101, 95, 102, 97, 115, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__290: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__290_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__291_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__291: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__291_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 105, 110, 116, 101, 114, 99, 97,
        108, 97, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__293_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__293: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__293_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__294_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__294: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__294_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__295_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__295: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__295_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 100, 114, 111, 112, 114, 105, 103,
        104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__299_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 102, 114, 111, 109, 95, 117, 116,
        102, 56, 95, 117, 110, 99, 104, 101, 99, 107, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__299: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__299_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__300_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__300: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__300_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__301_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__301: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__301_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__303_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__303: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__303_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 99, 97, 112, 105, 116, 97, 108,
        105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__305_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 99, 111, 109, 112, 97, 114, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__305: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__305_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 105, 110, 103, 95, 99, 111, 110, 116, 97, 105, 110,
        115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__307_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__307: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__307_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__308_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__308: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__308_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__309_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__309: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__309_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__310_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__310: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__310_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__311_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__311: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__311_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__312_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__312: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__312_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__313_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 97, 116, 101, 95, 115, 104, 97, 114, 101, 99, 111, 109,
        109, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__313: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__313_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__314_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 115, 104, 97, 114, 101, 99, 111, 109, 109, 111, 110, 95, 101, 113, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__314: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__314_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__315_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 115, 104, 97, 114, 101, 99, 111, 109, 109, 111, 110, 95, 104, 97,
        115, 104, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__315: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__315_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__316_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 115, 104, 97, 114, 101, 99, 111, 109, 109, 111, 110, 95, 113, 117,
        105, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__316: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__316_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__318_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__318: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__318_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__319_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__319: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__319_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__320_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__320: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__320_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__321_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 114, 117, 110, 95, 109, 111, 100, 95, 105, 110, 105, 116, 95, 99,
        111, 114, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__321: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__321_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__322_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 95, 102, 111, 114, 103, 101, 116,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__322: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__322_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__323_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__323: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__323_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__324_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 95, 109, 97, 114, 107, 95, 109,
        117, 108, 116, 105, 95, 116, 104, 114, 101, 97, 100, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__324: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__324_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__325_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 95, 109, 97, 114, 107, 95, 112,
        101, 114, 115, 105, 115, 116, 101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__325: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__325_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__326_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__326: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__326_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__327_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__327: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__327_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328_value:
    crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        108, 101, 97, 110, 95, 112, 114, 101, 116, 116, 121, 95, 112, 114, 105, 110, 116, 101, 114,
        95, 102, 111, 114, 109, 97, 116, 116, 101, 114, 95, 105, 110, 116, 101, 114, 112, 114, 101,
        116, 95, 112, 97, 114, 115, 101, 114, 95, 100, 101, 115, 99, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329_value:
    crate::leanh::LeanStringObject<57> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        108, 101, 97, 110, 95, 112, 114, 101, 116, 116, 121, 95, 112, 114, 105, 110, 116, 101, 114,
        95, 112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 95, 105, 110, 116, 101,
        114, 112, 114, 101, 116, 95, 112, 97, 114, 115, 101, 114, 95, 100, 101, 115, 99, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__330_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__330: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__330_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__331_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__331: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__331_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__332_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__332: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__332_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__333_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__333: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__333_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 114, 117, 110, 95, 105, 110, 105, 116, 95, 97, 116, 116, 114, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__335_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__335: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__335_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__336_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__336: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__336_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__337_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__337: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__337_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__338_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__338: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__338_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__339_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__339: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__339_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__340_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 111, 112, 116, 105, 111, 110, 95, 103, 101, 116, 95, 111, 114, 95,
        98, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__340: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__340_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__341_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__341: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__341_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__342_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__342: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__342_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__343_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__343: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__343_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__344_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__344: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__344_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__345_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__345: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__345_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__346_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__346: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__346_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__347_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__347: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__347_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__348_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__348: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__348_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__349_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__349: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__349_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__350_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__350: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__350_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__351_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__351: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__351_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__352_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__352: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__352_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__353_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__353: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__353_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__354_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__354: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__354_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__355_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__355: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__355_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__356_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__356: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__356_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 97, 110, 116, 105, 113, 117, 111, 116, 95, 112, 97,
        114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__358_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__358: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__358_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__359_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 97, 114, 114, 97, 121,
        95, 119, 105, 116, 104, 95, 99, 97, 112, 97, 99, 105, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__359: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__359_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__360_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 98, 121, 116, 101, 95,
        97, 114, 114, 97, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__360: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__360_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__361_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 102, 108, 111, 97, 116,
        95, 97, 114, 114, 97, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__361: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__361_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__362_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__362: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__362_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__363_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__363: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__363_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__364_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__364: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__364_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__365_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 118, 101, 114, 105, 102, 121, 95, 109, 111,
        100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__365: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__365_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__366_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 118, 111, 105, 100, 95, 116, 121, 112, 101,
        95, 105, 110, 95, 99, 111, 110, 116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__366: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__366_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__367_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 119, 114, 105, 116, 101, 95, 98, 105, 116,
        99, 111, 100, 101, 95, 116, 111, 95, 102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__367: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__367_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__368_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 109, 97, 110, 117, 97, 108, 95, 103, 101, 116, 95, 114, 111, 111,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__368: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__368_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__369_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__369: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__369_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 97, 110, 116, 105, 113, 117, 111, 116, 95, 102, 111,
        114, 109, 97, 116, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__371_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 114, 105, 110, 116, 95, 109, 111, 100,
        117, 108, 101, 95, 116, 111, 95, 115, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__371: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__371_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__372_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 100, 108, 108, 95, 115,
        116, 111, 114, 97, 103, 101, 95, 99, 108, 97, 115, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__372: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__372_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__373_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 105, 110, 105, 116, 105,
        97, 108, 105, 122, 101, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__373: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__373_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__374_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 108, 105, 110, 107, 97,
        103, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__374: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__374_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__375_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 116, 97, 105, 108, 95,
        99, 97, 108, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__375: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__375_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__376_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 115, 101, 116, 95, 118, 105, 115, 105, 98,
        105, 108, 105, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__376: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__376_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__377_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 116, 97, 114, 103, 101, 116, 95, 109, 97,
        99, 104, 105, 110, 101, 95, 101, 109, 105, 116, 95, 116, 111, 95, 102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__377: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__377_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__378_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 109, 111, 100, 117, 108, 101, 95, 116, 111,
        95, 115, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__378: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__378_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__379_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 111, 112, 97, 113, 117, 101, 95, 112, 111,
        105, 110, 116, 101, 114, 95, 116, 121, 112, 101, 95, 105, 110, 95, 99, 111, 110, 116, 101,
        120, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__379: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__379_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__380_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 97, 114, 115, 101, 95, 98, 105, 116,
        99, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__380: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__380_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__381_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 111, 105, 110, 116, 101, 114, 95, 116,
        121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__381: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__381_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__382_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 111, 115, 105, 116, 105, 111, 110, 95,
        98, 117, 105, 108, 100, 101, 114, 95, 97, 116, 95, 101, 110, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__382: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__382_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__383_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 111, 115, 105, 116, 105, 111, 110, 95,
        98, 117, 105, 108, 100, 101, 114, 95, 98, 101, 102, 111, 114, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__383: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__383_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__384_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 112, 114, 105, 110, 116, 95, 109, 111, 100,
        117, 108, 101, 95, 116, 111, 95, 102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__384: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__384_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__385_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 110, 101, 120, 116, 95,
        103, 108, 111, 98, 97, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__385: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__385_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__386_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 116, 97, 114, 103, 101,
        116, 95, 102, 114, 111, 109, 95, 116, 114, 105, 112, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__386: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__386_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__387_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 117, 110, 100, 101, 102,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__387: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__387_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__388_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 118, 97, 108, 117, 101,
        95, 110, 97, 109, 101, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__388: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__388_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__389_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 105, 110, 105, 116, 105, 97, 108, 105, 122,
        101, 95, 116, 97, 114, 103, 101, 116, 95, 105, 110, 102, 111, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__389: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__389_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__390_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 105, 110, 116, 95, 116, 121, 112, 101, 95,
        105, 110, 95, 99, 111, 110, 116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__390: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__390_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__391_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 108, 105, 110, 107, 95, 109, 111, 100, 117,
        108, 101, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__391: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__391_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__392_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 102, 105, 114, 115, 116,
        95, 102, 117, 110, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__392: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__392_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__393_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 102, 105, 114, 115, 116,
        95, 103, 108, 111, 98, 97, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__393: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__393_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__394_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 102, 105, 114, 115, 116,
        95, 105, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__394: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__394_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__395_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 105, 110, 115, 101, 114,
        116, 95, 98, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__395: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__395_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__396_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 110, 97, 109, 101, 100,
        95, 102, 117, 110, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__396: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__396_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__397_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 110, 97, 109, 101, 100,
        95, 103, 108, 111, 98, 97, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__397: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__397_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__398_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 110, 101, 120, 116, 95,
        102, 117, 110, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__398: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__398_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__399_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 102, 117, 110, 99, 116, 105, 111, 110, 95,
        116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__399: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__399_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__400_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 98, 97, 115, 105, 99, 95,
        98, 108, 111, 99, 107, 95, 112, 97, 114, 101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__400: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__400_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__401_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 100, 101, 102, 97, 117,
        108, 116, 95, 116, 97, 114, 103, 101, 116, 95, 116, 114, 105, 112, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__401: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__401_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__402_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 103, 101, 116, 95, 101, 110, 116, 114, 121,
        95, 98, 97, 115, 105, 99, 95, 98, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__402: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__402_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__403_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 100, 105, 115, 112, 111, 115, 101, 95, 109,
        111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__403: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__403_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__404_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 100, 105, 115, 112, 111, 115, 101, 95, 116,
        97, 114, 103, 101, 116, 95, 109, 97, 99, 104, 105, 110, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__404: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__404_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__405_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 100, 111, 117, 98, 108, 101, 95, 116, 121,
        112, 101, 95, 105, 110, 95, 99, 111, 110, 116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__405: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__405_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__406_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 102, 108, 111, 97, 116, 95, 116, 121, 112,
        101, 95, 105, 110, 95, 99, 111, 110, 116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__406: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__406_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__407_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__407: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__407_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__408_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__408: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__408_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__409_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__409: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__409_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__410_value:
    crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 114, 101, 97, 116, 101, 95, 109, 101,
        109, 111, 114, 121, 95, 98, 117, 102, 102, 101, 114, 95, 119, 105, 116, 104, 95, 99, 111,
        110, 116, 101, 110, 116, 115, 95, 111, 102, 95, 102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__410: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__410_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__411_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 114, 101, 97, 116, 101, 95, 109, 111,
        100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__411: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__411_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__412_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 114, 101, 97, 116, 101, 95, 115, 116,
        114, 105, 110, 103, 95, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__412: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__412_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__413_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__413: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__413_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__414_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 117, 110, 114,
        101, 97, 99, 104, 97, 98, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__414: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__414_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__415_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 122, 101, 120,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__415: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__415_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__416_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 108, 101, 97, 114, 95, 105, 110, 115,
        101, 114, 116, 105, 111, 110, 95, 112, 111, 115, 105, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__416: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__416_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__417_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 111, 110, 115, 116, 95, 97, 114, 114,
        97, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__417: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__417_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__418_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 111, 110, 115, 116, 95, 105, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__418: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__418_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__419_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 111, 110, 115, 116, 95, 112, 111, 105,
        110, 116, 101, 114, 95, 110, 117, 108, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__419: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__419_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__420_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 99, 111, 110, 115, 116, 95, 115, 116, 114,
        105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__420: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__420_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__421_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 112, 116, 114,
        95, 116, 111, 95, 105, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__421: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__421_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__422_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 114, 101, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__422: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__422_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__423_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 101, 120,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__423: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__423_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__424_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 101, 120,
        116, 95, 111, 114, 95, 116, 114, 117, 110, 99, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__424: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__424_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__425_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 116, 111,
        114, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__425: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__425_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__426_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 117, 98, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__426: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__426_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__427_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 115, 119, 105,
        116, 99, 104, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__427: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__427_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__428_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 103, 101, 112,
        50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__428: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__428_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__429_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 103, 108, 111,
        98, 97, 108, 95, 115, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__429: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__429_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__430_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 105, 99, 109,
        112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__430: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__430_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__431_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 105, 110, 98,
        111, 117, 110, 100, 115, 95, 103, 101, 112, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__431: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__431_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__432_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 108, 111, 97,
        100, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__432: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__432_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__433_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 109, 117, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__433: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__433_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__434_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 110, 111, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__434: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__434_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__435_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__435: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__435_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__436_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 97, 114, 114, 97, 121, 95, 116, 121, 112,
        101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__436: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__436_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__437_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 97, 100, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__437: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__437_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__438_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 97, 108, 108,
        111, 99, 97, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__438: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__438_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__439_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__439: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__439_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__440_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__440: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__440_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__441_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 98, 117, 105, 108, 100, 95, 99, 111, 110,
        100, 95, 98, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__441: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__441_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__442_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__442: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__442_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__443_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__443: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__443_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__444_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__444: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__444_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__445_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 97, 100, 100, 95, 97, 116, 116, 114, 105,
        98, 117, 116, 101, 95, 97, 116, 95, 105, 110, 100, 101, 120, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__445: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__445_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__446_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__446: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__446_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__447_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 108, 108, 118, 109, 95, 97, 100, 100, 95, 102, 117, 110, 99, 116,
        105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__447: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__447_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__448_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__448: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__448_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__449_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 105, 110, 116, 51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__449: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__449_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__450_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 105, 110, 116, 54, 52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__450: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__450_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__451_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__451: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__451_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__452_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__452: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__452_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__453_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__453: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__453_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__454_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 105, 115, 95, 100, 101, 102, 95,
        101, 113, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__454: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__454_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__455_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__455: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__455_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__456_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 102, 108, 111, 97, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__456: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__456_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__457_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 102, 108, 111, 97, 116,
        51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__457: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__457_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__458_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__458: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__458_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__459_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 116, 111, 95, 105, 110, 116, 49, 54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__459: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__459_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__460_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__460: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__460_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__461_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 115, 104, 105, 102, 116, 95, 108, 101,
        102, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__461: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__461_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__462_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 115, 104, 105, 102, 116, 95, 114, 105,
        103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__462: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__462_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__463_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__463: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__463_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__464_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__464: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__464_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__465_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__465: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__465_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__466_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__466: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__466_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__467_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__467: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__467_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__468_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__468: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__468_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__469_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__469: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__469_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__470_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__470: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__470_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__471_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__471: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__471_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__472_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__472: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__472_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__473_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__473: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__473_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__474_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 105, 122, 101, 95, 99, 111, 109, 112, 108, 101, 109, 101,
        110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__474: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__474_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__475_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__475: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__475_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__476_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__476: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__476_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__477_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__477: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__477_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__478_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__478: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__478_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__479_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__479: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__479_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 114, 95, 101, 120, 112, 111, 114, 116, 95, 101, 110, 116, 114,
        105, 101, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__481_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 95, 101, 120, 99, 108, 117, 115, 105, 118, 101, 95, 111,
        98, 106, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__481: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__481_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 95, 101, 120, 112, 114, 95, 100, 101, 102, 95, 101, 113, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 95, 108, 101, 118, 101, 108, 95, 100, 101, 102, 95, 101,
        113, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 95, 114, 101, 115, 101, 114, 118, 101, 100, 95, 110, 97,
        109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__485_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__485: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__485_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__486_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__486: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__486_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__487_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 114, 101, 109, 111, 118, 101, 95, 102, 105, 108, 101,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__487: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__487_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__488_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__488: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__488_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__489_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 115, 101, 116, 95, 104, 101, 97, 114, 116, 98, 101,
        97, 116, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__489: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__489_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__490_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 115, 121, 109, 108, 105, 110, 107, 95, 109, 101, 116,
        97, 100, 97, 116, 97, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__490: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__490_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__491_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__491: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__491_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__492_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 103, 101, 116,
        95, 112, 105, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__492: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__492_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__493_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 115, 101, 116,
        95, 99, 117, 114, 114, 101, 110, 116, 95, 100, 105, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__493: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__493_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__494_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 115, 112, 97,
        119, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__494: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__494_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__495_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 109, 105, 115, 101, 95, 110, 101, 119,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__495: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__495_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__496_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 109, 105, 115, 101, 95, 114, 101, 115,
        111, 108, 118, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__496: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__496_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__497_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 109, 105, 115, 101, 95, 114, 101, 115,
        117, 108, 116, 95, 111, 112, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__497: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__497_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__498_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__498: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__498_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__499_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 119, 114, 105, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__499: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__499_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__500_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104, 105,
        108, 100, 95, 107, 105, 108, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__500: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__500_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__501_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104, 105,
        108, 100, 95, 112, 105, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__501: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__501_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__502_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104, 105,
        108, 100, 95, 116, 97, 107, 101, 95, 115, 116, 100, 105, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__502: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__502_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__503_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104, 105,
        108, 100, 95, 116, 114, 121, 95, 119, 97, 105, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__503: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__503_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__504_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 99, 104, 105,
        108, 100, 95, 119, 97, 105, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__504: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__504_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__505_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 111, 99, 101, 115, 115, 95, 103, 101, 116,
        95, 99, 117, 114, 114, 101, 110, 116, 95, 100, 105, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__505: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__505_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__506_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 109, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__506: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__506_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__507_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 112, 117, 116, 95, 115, 116, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__507: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__507_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__508_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 114, 101, 97, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__508: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__508_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__509_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 114, 101, 119, 105, 110, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__509: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__509_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__510_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 116, 114, 117, 110, 99, 97, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__510: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__510_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__511_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 116, 114, 121, 95, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__511: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__511_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__512_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 117, 110, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__512: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__512_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__513_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 102, 108, 117, 115, 104, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__513: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__513_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__514_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 103, 101, 116, 95, 108, 105, 110, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__514: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__514_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__515_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 105, 115, 95, 116, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__515: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__515_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__516_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 112, 114, 105, 109, 95, 104, 97, 110, 100, 108, 101,
        95, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__516: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__516_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__517_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__517: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__517_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__518_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__518: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__518_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__519_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 109, 111, 110, 111, 95, 109, 115, 95, 110, 111, 119, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__519: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__519_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__520_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 109, 111, 110, 111, 95, 110, 97, 110, 111, 115, 95,
        110, 111, 119, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__520: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__520_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__521_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 103, 101, 116, 95, 110, 117, 109, 95, 104, 101, 97,
        114, 116, 98, 101, 97, 116, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__521: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__521_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__522_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 103, 101, 116, 95, 114, 97, 110, 100, 111, 109, 95,
        98, 121, 116, 101, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__522: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__522_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__523_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 103, 101, 116, 95, 116, 97, 115, 107, 95, 115, 116,
        97, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__523: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__523_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__524_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__524: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__524_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__525_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__525: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__525_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__526_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__526: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__526_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__527_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 105, 110, 105, 116, 105, 97, 108, 105, 122, 105, 110,
        103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__527: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__527_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__528_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__528: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__528_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__529_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__529: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__529_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__530_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 99, 114, 101, 97, 116, 101, 95, 116, 101, 109, 112,
        100, 105, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__530: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__530_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__531_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 99, 114, 101, 97, 116, 101, 95, 116, 101, 109, 112,
        102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__531: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__531_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__532_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 99, 117, 114, 114, 101, 110, 116, 95, 100, 105, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__532: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__532_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__533_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__533: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__533_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__534_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__534: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__534_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__535_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100, 109,
        117, 116, 101, 120, 95, 119, 114, 105, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__535: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__535_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__536_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__536: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__536_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__537_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__537: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__537_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__538_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 99, 104, 101, 99, 107, 95, 99, 97, 110, 99, 101, 108,
        101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__538: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__538_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__539_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 99, 111, 110, 100, 118, 97, 114, 95, 110, 101, 119, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__539: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__539_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__540_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 99, 111, 110, 100, 118, 97, 114, 95, 110, 111, 116,
        105, 102, 121, 95, 97, 108, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__540: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__540_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__541_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 99, 111, 110, 100, 118, 97, 114, 95, 110, 111, 116,
        105, 102, 121, 95, 111, 110, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__541: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__541_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__542_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 114, 101, 99, 109, 117, 116, 101,
        120, 95, 117, 110, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__542: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__542_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__543_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100, 109,
        117, 116, 101, 120, 95, 110, 101, 119, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__543: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__543_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__544_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100, 109,
        117, 116, 101, 120, 95, 114, 101, 97, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__544: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__544_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__545_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100, 109,
        117, 116, 101, 120, 95, 116, 114, 121, 95, 114, 101, 97, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__545: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__545_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__546_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100, 109,
        117, 116, 101, 120, 95, 116, 114, 121, 95, 119, 114, 105, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__546: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__546_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__547_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100, 109,
        117, 116, 101, 120, 95, 117, 110, 108, 111, 99, 107, 95, 114, 101, 97, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__547: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__547_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__548_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 115, 104, 97, 114, 101, 100, 109,
        117, 116, 101, 120, 95, 117, 110, 108, 111, 99, 107, 95, 119, 114, 105, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__548: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__548_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__549_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 109, 117, 116, 101, 120, 95, 108,
        111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__549: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__549_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__550_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 109, 117, 116, 101, 120, 95, 110,
        101, 119, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__550: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__550_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__551_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 109, 117, 116, 101, 120, 95, 116,
        114, 121, 95, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__551: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__551_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__552_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 109, 117, 116, 101, 120, 95, 117,
        110, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__552: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__552_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__553_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 114, 101, 99, 109, 117, 116, 101,
        120, 95, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__553: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__553_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__554_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 114, 101, 99, 109, 117, 116, 101,
        120, 95, 110, 101, 119, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__554: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__554_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__555_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 98, 97, 115, 101, 114, 101, 99, 109, 117, 116, 101,
        120, 95, 116, 114, 121, 95, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__555: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__555_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__556_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 115, 101, 116, 95, 101,
        120, 105, 116, 95, 111, 110, 95, 112, 97, 110, 105, 99, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__556: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__556_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__557_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 115, 101, 116, 95, 109,
        97, 120, 95, 104, 101, 97, 114, 116, 98, 101, 97, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__557: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__557_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__558_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 115, 101, 116, 95, 109,
        97, 120, 95, 109, 101, 109, 111, 114, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__558: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__558_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__559_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 115, 101, 116, 95, 116,
        104, 114, 101, 97, 100, 95, 115, 116, 97, 99, 107, 95, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__559: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__559_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__560_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__560: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__560_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__561_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__561: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__561_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__562_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__562: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__562_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__563_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95, 100,
        101, 102, 97, 117, 108, 116, 95, 118, 101, 114, 98, 111, 115, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__563: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__563_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__564_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95, 104,
        97, 114, 100, 119, 97, 114, 101, 95, 99, 111, 110, 99, 117, 114, 114, 101, 110, 99, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__564: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__564_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__565_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__565: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__565_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__566_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 104, 97, 115, 95, 108,
        108, 118, 109, 95, 98, 97, 99, 107, 101, 110, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__566: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__566_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__567_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 105, 115, 95, 100, 101,
        98, 117, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__567: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__567_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__568_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 105, 115, 95, 109, 117,
        108, 116, 105, 95, 116, 104, 114, 101, 97, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__568: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__568_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__569_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 105, 115, 95, 115, 116,
        97, 103, 101, 48, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__569: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__569_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__570_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95, 98,
        117, 105, 108, 100, 95, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__570: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__570_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__571_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95, 100,
        101, 102, 97, 117, 108, 116, 95, 109, 97, 120, 95, 104, 101, 97, 114, 116, 98, 101, 97,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__571: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__571_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__572_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95, 100,
        101, 102, 97, 117, 108, 116, 95, 109, 97, 120, 95, 109, 101, 109, 111, 114, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__572: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__572_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__573_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95, 100,
        101, 102, 97, 117, 108, 116, 95, 111, 112, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__573: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__573_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__574_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__574: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__574_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__575_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__575: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__575_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__576_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 101, 110, 97, 98, 108,
        101, 95, 100, 101, 98, 117, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__576: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__576_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__577_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 103, 101, 116, 95, 98,
        101, 108, 105, 101, 118, 101, 114, 95, 116, 114, 117, 115, 116, 95, 108, 101, 118, 101,
        108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__577: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__577_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__578_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__578: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__578_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__579_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__579: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__579_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__580_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 116, 111, 95, 102, 108, 111, 97, 116, 51, 50,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__580: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__580_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__581_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__581: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__581_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__582_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__582: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__582_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__583_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__583: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__583_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__584_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__584: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__584_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__585_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__585: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__585_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__586_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__586: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__586_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__587_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__587: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__587_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__588_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__588: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__588_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__589_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__589: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__589_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__590_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 115, 104, 105, 102, 116, 95, 108, 101, 102,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__590: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__590_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__591_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 115, 104, 105, 102, 116, 95, 114, 105, 103,
        104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__591: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__591_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__592_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 56, 95, 99, 111, 109, 112, 108, 101, 109, 101, 110,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__592: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__592_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__593_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__593: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__593_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__594_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__594: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__594_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__595_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__595: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__595_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__596_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__596: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__596_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__597_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__597: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__597_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__598_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__598: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__598_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__599_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 105, 110, 116, 49, 54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__599: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__599_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__600_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 105, 110, 116, 51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__600: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__600_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__601_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__601: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__601_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__602_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 105, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__602: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__602_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__603_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__603: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__603_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__604_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__604: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__604_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__605_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__605: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__605_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__606_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__606: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__606_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__607_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 115, 104, 105, 102, 116, 95, 108, 101,
        102, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__607: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__607_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__608_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 115, 104, 105, 102, 116, 95, 114, 105,
        103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__608: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__608_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__609_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__609: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__609_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__610_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 102, 108, 111, 97, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__610: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__610_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__611_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 116, 111, 95, 102, 108, 111, 97, 116, 51,
        50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__611: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__611_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__612_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__612: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__612_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__613_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__613: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__613_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__614_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__614: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__614_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__615_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__615: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__615_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__616_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__616: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__616_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__617_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__617: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__617_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__618_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__618: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__618_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__619_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__619: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__619_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__620_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__620: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__620_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__621_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__621: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__621_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__622_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__622: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__622_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__623_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 54, 52, 95, 99, 111, 109, 112, 108, 101, 109, 101,
        110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__623: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__623_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__624_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__624: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__624_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__625_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__625: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__625_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__626_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__626: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__626_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__627_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 49, 54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__627: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__627_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__628_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 54, 52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__628: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__628_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__629_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__629: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__629_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__630_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 105, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__630: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__630_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__631_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__631: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__631_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__632_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 102, 108, 111, 97, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__632: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__632_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__633_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 116, 111, 95, 102, 108, 111, 97, 116, 51,
        50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__633: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__633_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__634_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__634: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__634_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__635_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__635: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__635_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__636_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__636: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__636_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__637_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__637: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__637_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__638_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__638: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__638_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__639_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__639: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__639_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__640_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 115, 104, 105, 102, 116, 95, 108, 101,
        102, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__640: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__640_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__641_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 115, 104, 105, 102, 116, 95, 114, 105,
        103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__641: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__641_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__642_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 51, 50, 95, 99, 111, 109, 112, 108, 101, 109, 101,
        110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__642: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__642_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__643_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__643: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__643_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__644_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__644: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__644_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__645_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__645: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__645_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__646_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__646: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__646_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__647_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__647: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__647_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__648_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__648: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__648_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__649_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 105, 110, 116, 51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__649: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__649_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__650_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 105, 110, 116, 54, 52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__650: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__650_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__651_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__651: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__651_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__652_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 105, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__652: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__652_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__653_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__653: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__653_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__654_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__654: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__654_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__655_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__655: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__655_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__656_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__656: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__656_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__657_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 115, 104, 105, 102, 116, 95, 108, 101,
        102, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__657: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__657_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__658_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 115, 104, 105, 102, 116, 95, 114, 105,
        103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__658: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__658_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__659_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__659: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__659_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__660_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 102, 108, 111, 97, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__660: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__660_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__661_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 116, 111, 95, 102, 108, 111, 97, 116, 51,
        50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__661: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__661_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__662_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__662: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__662_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__663_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__663: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__663_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__664_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__664: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__664_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__665_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__665: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__665_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__666_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__666: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__666_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__667_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__667: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__667_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__668_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__668: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__668_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__669_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__669: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__669_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__670_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__670: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__670_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__671_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__671: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__671_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__672_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__672: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__672_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__673_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 49, 54, 95, 99, 111, 109, 112, 108, 101, 109, 101,
        110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__673: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__673_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__674_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__674: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__674_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__675_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__675: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__675_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__676_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__676: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__676_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__677_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__677: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__677_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__678_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__678: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__678_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__679_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__679: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__679_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__680_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__680: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__680_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__681_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__681: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__681_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__682_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__682: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__682_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__683_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__683: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__683_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__684_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__684: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__684_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__685_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__685: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__685_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__686_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 116, 95, 100, 101, 99, 95, 110, 111, 110, 110, 101, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__686: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__686_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__687_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__687: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__687_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__688_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 95, 101, 120,
        112, 114, 95, 109, 118, 97, 114, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__688: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__688_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__689_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 95, 108, 101,
        118, 101, 108, 95, 109, 118, 97, 114, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__689: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__689_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__690_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__690: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__690_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__691_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__691: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__691_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 110, 111, 114, 109, 97, 108, 105, 122,
        101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 112, 114, 101, 112, 114, 111, 99, 101,
        115, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 112, 114, 111, 99, 101, 115, 115, 95,
        110, 101, 119, 95, 102, 97, 99, 116, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 104, 97, 115, 95, 99, 111, 109, 112, 105, 108, 101, 95, 101, 114,
        114, 111, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 100, 98, 103, 95, 99, 108, 105, 101, 110, 116, 95, 108, 111,
        111, 112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__698_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__698: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__698_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__699_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 119, 105, 110, 100, 111, 119, 115, 95, 108, 111,
        99, 97, 108, 95, 116, 105, 109, 101, 122, 111, 110, 101, 95, 105, 100, 95, 97, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__699: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__699_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 99, 117, 116, 115, 97, 116, 95, 109,
        107, 95, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 105, 110, 116, 101, 114, 110, 97, 108,
        105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 109, 107, 95, 101, 113, 95, 112, 114,
        111, 111, 102, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 103, 114, 105, 110, 100, 95, 109, 107, 95, 104, 101, 113, 95, 112,
        114, 111, 111, 102, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__706_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__706: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__706_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__707_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 101, 116, 95, 115, 116, 100, 111, 117, 116,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__707: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__707_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__708_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__708: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__708_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__709_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__709: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__709_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__710_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__710: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__710_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108,
        95, 114, 101, 99, 95, 97, 114, 103, 95, 112, 111, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__712_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 117, 115, 105, 122, 101, 95, 115, 105, 122, 101,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__712: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__712_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__713_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 108, 105, 110, 107, 101, 114, 95, 102, 108, 97,
        103, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__713: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__713_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__715_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__715: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__715_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__716_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 109, 97, 120, 95, 99, 116, 111, 114, 95, 115, 99,
        97, 108, 97, 114, 115, 95, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__716: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__716_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__717_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 109, 97, 120, 95, 99, 116, 111, 114, 95, 116, 97,
        103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__717: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__717_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 110, 117, 109, 95, 97, 116, 116, 114, 105, 98,
        117, 116, 101, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__719_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 101, 116, 95, 115, 116, 100, 101, 114, 114,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__719: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__719_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__721_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 99, 117, 114, 114, 101, 110, 116, 95, 116, 105,
        109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__721: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__721_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__722_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__722: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__722_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__723_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 105, 110, 116, 101, 114, 110, 97, 108, 95, 108,
        105, 110, 107, 101, 114, 95, 102, 108, 97, 103, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__723: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__723_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__725_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 108, 101, 97, 110, 99, 95, 101, 120, 116, 114,
        97, 95, 102, 108, 97, 103, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__725: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__725_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__726_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 108, 101, 97, 110, 99, 95, 105, 110, 116, 101,
        114, 110, 97, 108, 95, 102, 108, 97, 103, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__726: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__726_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__727_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__727: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__727_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__728_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__728: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__728_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__729_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__729: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__729_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__730_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__730: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__730_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__731_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__731: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__731_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__732_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__732: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__732_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__733_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__733: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__733_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__734_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__734: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__734_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__735_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 98, 105, 116, 115,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__735: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__735_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__736_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 102, 108, 111, 97,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__736: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__736_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__737_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 49,
        54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__737: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__737_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__738_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 51,
        50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__738: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__738_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__739_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 54,
        52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__739: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__739_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__740_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 116, 111, 95, 105, 110, 116, 56,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__740: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__740_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__741_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__741: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__741_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__742_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 110, 101, 103, 97, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__742: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__742_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__743_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 111, 102, 95, 98, 105, 116, 115,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__743: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__743_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__744_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__744: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__744_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__745_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__745: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__745_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__746_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 105, 115, 102, 105, 110, 105,
        116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__746: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__746_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__747_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__747: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__747_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__748_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__748: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__748_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__749_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 105, 110, 116, 56, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__749: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__749_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__750_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__750: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__750_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__751_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__751: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__751_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__752_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__752: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__752_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__753_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__753: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__753_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__754_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__754: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__754_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__755_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__755: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__755_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__756_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 105, 110, 116, 54, 52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__756: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__756_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__757_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__757: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__757_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__758_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 105, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__758: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__758_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__759_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 115, 116, 114, 105, 110,
        103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__759: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__759_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__760_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 105, 110, 116, 49,
        54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__760: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__760_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__761_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 105, 110, 116, 51,
        50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__761: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__761_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__762_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 117, 105, 110, 116, 54,
        52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__762: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__762_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__763_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__763: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__763_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__764_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__764: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__764_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__765_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__765: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__765_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__766_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__766: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__766_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__767_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 102, 108, 111, 97, 116,
        51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__767: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__767_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__768_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 105, 110, 116, 49, 54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__768: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__768_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__769_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 116, 111, 95, 105, 110, 116, 51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__769: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__769_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__770_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__770: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__770_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__771_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__771: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__771_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__772_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 105, 115, 102, 105, 110, 105, 116, 101,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__772: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__772_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__773_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__773: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__773_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__774_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__774: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__774_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__775_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__775: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__775_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__776_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__776: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__776_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__777_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__777: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__777_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__778_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__778: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__778_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__779_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__779: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__779_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__780_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__780: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__780_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__781_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__781: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__781_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__782_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__782: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__782_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__783_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__783: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__783_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__784_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__784: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__784_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__785_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 100, 97, 116,
        97, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__785: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__785_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__786_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__786: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__786_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__787_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__787: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__787_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__788_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__788: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__788_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__789_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 95, 97, 114, 114, 97, 121, 95, 109, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__789: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__789_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__790_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__790: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__790_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__791_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 108, 111, 119, 101, 114, 95, 108, 111, 111,
        115, 101, 95, 98, 118, 97, 114, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__791: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__791_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__792_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__792: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__792_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__793_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__793: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__793_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__794_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__794: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__794_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__795_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__795: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__795_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__796_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__796: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__796_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__797_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__797: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__797_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__798_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105, 97,
        116, 101, 95, 114, 101, 118, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__798: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__798_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__799_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105, 97,
        116, 101, 95, 114, 101, 118, 95, 114, 97, 110, 103, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__799: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__799_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__800_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105, 97,
        116, 101, 49, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__800: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__800_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__801_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 108, 105, 102, 116, 95, 108, 111, 111, 115,
        101, 95, 98, 118, 97, 114, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__801: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__801_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__802_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__802: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__802_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__803_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 108, 111, 111, 115, 101,
        95, 98, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__803: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__803_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__804_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105, 97,
        116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__804: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__804_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__805_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 105, 110, 115, 116, 97, 110, 116, 105, 97,
        116, 101, 95, 114, 97, 110, 103, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__805: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__805_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__806_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__806: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__806_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 101, 118, 97, 108, 95, 115, 117, 103, 103, 101, 115, 116, 95, 116,
        97, 99, 116, 105, 99, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__808_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__808: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__808_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__809_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 97, 98, 115, 116, 114, 97, 99, 116, 95, 114,
        97, 110, 103, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__809: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__809_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__810_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__810: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__810_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__811_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 100, 98, 103, 95, 116, 111, 95, 115, 116,
        114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__811: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__811_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__812_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__812: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__812_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__813_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__813: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__813_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__814_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 100, 121, 110, 108, 105, 98, 95, 115, 121, 109, 98, 111, 108, 95,
        114, 117, 110, 95, 97, 115, 95, 105, 110, 105, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__814: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__814_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__815_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__815: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__815_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__816_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 101, 108, 97, 98, 95, 97, 100, 100, 95, 100, 101, 99, 108, 95, 119,
        105, 116, 104, 111, 117, 116, 95, 99, 104, 101, 99, 107, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__816: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__816_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__817_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__817: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__817_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 101, 118, 97, 108, 95, 99, 104, 101, 99, 107, 95, 109, 101, 116, 97,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__819_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__819: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__819_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__820_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 100, 98, 103, 95, 115, 116, 97, 99, 107, 95, 116, 114, 97, 99, 101,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__820: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__820_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__821_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__821: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__821_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__822_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 100, 98, 103, 95, 116, 114, 97, 99, 101, 95, 105, 102, 95, 115, 104,
        97, 114, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__822: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__822_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__823_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 100, 101, 99, 111, 100, 101, 95, 108, 111, 115, 115, 121, 95, 117,
        116, 102, 56, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__823: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__823_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__824_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        108, 101, 97, 110, 95, 100, 105, 115, 112, 108, 97, 121, 95, 99, 117, 109, 117, 108, 97,
        116, 105, 118, 101, 95, 112, 114, 111, 102, 105, 108, 105, 110, 103, 95, 116, 105, 109,
        101, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__824: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__824_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__826_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__826: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__826_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__827_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103, 105,
        111, 110, 95, 105, 115, 95, 109, 101, 109, 111, 114, 121, 95, 109, 97, 112, 112, 101, 100,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__827: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__827_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__828_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103, 105,
        111, 110, 95, 114, 101, 97, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__828: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__828_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__829_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103, 105,
        111, 110, 95, 115, 97, 118, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__829: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__829_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__830_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103, 105,
        111, 110, 95, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__830: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__830_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__833_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__833: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__833_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__834_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__834: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__834_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__835_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__835: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__835_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__836_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__836: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__836_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 99, 104, 101, 99, 107, 101, 100, 95, 97, 115, 115, 105, 103, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__838_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__838: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__838_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__839_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__839: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__839_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__840_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 99, 111, 109, 112, 97, 99, 116, 101, 100, 95, 114, 101, 103, 105,
        111, 110, 95, 102, 114, 101, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__840: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__840_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__841_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__841: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__841_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__842_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 103, 101, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__842: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__842_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__843_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 104, 97, 115, 104,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__843: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__843_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__844_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__844: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__844_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__845_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__845: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__845_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__846_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 115, 101, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__846: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__846_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__847_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__847: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__847_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__848_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 117, 105, 110, 116, 51, 50, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__848: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__848_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__849_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 117, 105, 110, 116, 54, 52, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__849: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__849_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__850_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__850: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__850_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__851_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__851: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__851_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__852_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 99, 111, 112, 121,
        95, 115, 108, 105, 99, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__852: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__852_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__853_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 98, 121, 116, 101, 95, 97, 114, 114, 97, 121, 95, 100, 97, 116, 97,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__853: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__853_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__854_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__854: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__854_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__855_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__855: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__855_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__856_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__856: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__856_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__857_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__857: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__857_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__858_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__858: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__858_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__859_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__859: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__859_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__860_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__860: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__860_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__861_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 98, 111, 111, 108, 95, 116, 111, 95, 117, 105, 110, 116, 49, 54, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__861: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__861_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__862_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__862: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__862_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__863_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__863: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__863_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__864_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__864: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__864_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__865_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__865: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__865_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__866_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__866: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__866_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__867_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__867: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__867_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__868_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__868: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__868_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__869_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__869: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__869_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__870_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__870: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__870_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__871_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__871: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__871_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__872_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__872: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__872_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__873_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 97, 114, 114, 97, 121, 95, 103, 101, 116, 95, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__873: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__873_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__874_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__874: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__874_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__875_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__875: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__875_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__876_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__876: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__876_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__877_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__877: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__877_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 97, 107, 101, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 97, 100,
        100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__879_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__879: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__879_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__880_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 97, 100, 100, 95, 100, 101, 99, 108, 95, 119, 105, 116, 104, 111,
        117, 116, 95, 99, 104, 101, 99, 107, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__880: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__880_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__881_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__881: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__881_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__882_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__882: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__882_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__883_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__883: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__883_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__884_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__884: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__884_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__885_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__885: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__885_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__886_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__886: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__886_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__887_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__887: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__887_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__888_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__888: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__888_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__889_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__889: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__889_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__890_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__890: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__890_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__891_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__891: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__891_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__892_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__892: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__892_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__893_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__893: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__893_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__894_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__894: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__894_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__895_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__895: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__895_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__896_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__896: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__896_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__897_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__897: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__897_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__898_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__898: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__898_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__899_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__899: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__899_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__900_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__900: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__900_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__901_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__901: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__901_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__902_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__902: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__902_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__903_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__903: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__903_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__904_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__904: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__904_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__905_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__905: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__905_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__906_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__906: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__906_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__907_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__907: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__907_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__908_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__908: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__908_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__909_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__909: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__909_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__910_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__910: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__910_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_leanImportsFromRust___closed__911_value:
    crate::leanh::LeanArrayObject<911> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 911) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 911,
    m_capacity: 911,
    m_data: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__904_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__905_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__906_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__907_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__908_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__909_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__910_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__897_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__898_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__899_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__900_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__901_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__902_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__903_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__890_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__891_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__892_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__893_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__894_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__895_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__896_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__883_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__884_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__885_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__886_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__887_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__888_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__889_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__876_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__877_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__879_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__880_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__881_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__882_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__869_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__870_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__871_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__872_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__873_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__874_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__875_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__862_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__863_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__864_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__865_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__866_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__867_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__868_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__855_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__856_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__857_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__858_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__859_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__860_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__861_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__848_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__849_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__850_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__851_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__852_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__853_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__854_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__841_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__842_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__843_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__844_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__845_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__846_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__847_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__834_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__835_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__836_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__838_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__839_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__840_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__827_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__828_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__829_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__830_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__833_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__820_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__821_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__822_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__823_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__824_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__826_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__813_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__814_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__815_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__816_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__817_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__819_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__806_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__808_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__809_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__810_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__811_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__812_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__802_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__803_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__804_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__805_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__798_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__799_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__800_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__801_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__791_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__792_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__793_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__794_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__795_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__796_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__797_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__784_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__785_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__786_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__787_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__788_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__789_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__790_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__777_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__778_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__779_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__780_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__781_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__782_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__783_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__770_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__771_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__772_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__773_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__774_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__775_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__776_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__763_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__764_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__765_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__766_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__767_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__768_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__769_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__756_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__757_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__758_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__759_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__760_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__761_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__762_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__749_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__750_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__751_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__752_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__753_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__754_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__755_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__745_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__746_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__747_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__748_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__741_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__742_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__743_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__744_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__734_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__735_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__736_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__737_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__738_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__739_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__740_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__727_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__728_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__729_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__730_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__731_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__732_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__733_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__721_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__722_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__723_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__725_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__726_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__713_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__715_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__716_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__717_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__719_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__706_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__707_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__708_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__709_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__710_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__712_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__699_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__698_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__688_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__689_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__690_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__691_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__684_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__685_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__686_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__687_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__677_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__678_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__679_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__680_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__681_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__682_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__683_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__670_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__671_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__672_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__673_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__674_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__675_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__676_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__663_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__664_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__665_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__666_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__667_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__668_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__669_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__656_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__657_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__658_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__659_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__660_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__661_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__662_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__649_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__650_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__651_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__652_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__653_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__654_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__655_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__642_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__643_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__644_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__645_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__646_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__647_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__648_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__635_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__636_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__637_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__638_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__639_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__640_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__641_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__631_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__632_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__633_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__634_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__627_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__628_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__629_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__630_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__620_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__621_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__622_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__623_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__624_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__625_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__626_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__613_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__614_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__615_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__616_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__617_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__618_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__619_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__606_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__607_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__608_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__609_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__610_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__611_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__612_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__599_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__600_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__601_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__602_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__603_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__604_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__605_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__592_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__593_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__594_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__595_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__596_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__597_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__598_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__585_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__586_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__587_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__588_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__589_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__590_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__591_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__578_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__579_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__580_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__581_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__582_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__583_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__584_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__574_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__575_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__576_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__577_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__570_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__571_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__572_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__573_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__563_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__564_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__565_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__566_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__567_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__568_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__569_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__556_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__557_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__558_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__559_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__560_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__561_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__562_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__549_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__550_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__551_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__552_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__553_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__554_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__555_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__542_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__543_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__544_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__545_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__546_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__547_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__548_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__535_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__536_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__537_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__538_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__539_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__540_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__541_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__528_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__529_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__530_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__531_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__532_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__533_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__534_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__521_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__522_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__523_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__524_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__525_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__526_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__527_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__517_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__518_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__519_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__520_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__513_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__514_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__515_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__516_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__506_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__507_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__508_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__509_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__510_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__511_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__512_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__499_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__500_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__501_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__502_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__503_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__504_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__505_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__492_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__493_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__494_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__495_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__496_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__497_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__498_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__485_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__486_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__487_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__488_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__489_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__490_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__491_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__478_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__479_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__481_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__471_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__472_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__473_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__474_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__475_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__476_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__477_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__464_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__465_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__466_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__467_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__468_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__469_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__470_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__460_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__461_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__462_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__463_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__456_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__457_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__458_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__459_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__449_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__450_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__451_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__452_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__453_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__454_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__455_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__442_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__443_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__444_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__445_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__446_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__447_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__448_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__435_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__436_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__437_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__438_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__439_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__440_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__441_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__428_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__429_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__430_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__431_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__432_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__433_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__434_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__421_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__422_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__423_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__424_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__425_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__426_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__427_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__414_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__415_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__416_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__417_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__418_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__419_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__420_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__407_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__408_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__409_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__410_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__411_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__412_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__413_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__403_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__404_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__405_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__406_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__399_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__400_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__401_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__402_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__392_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__393_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__394_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__395_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__396_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__397_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__398_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__385_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__386_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__387_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__388_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__389_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__390_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__391_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__378_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__379_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__380_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__381_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__382_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__383_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__384_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__371_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__372_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__373_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__374_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__375_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__376_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__377_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__364_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__365_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__366_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__367_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__368_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__369_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__358_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__359_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__360_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__361_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__362_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__363_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__350_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__351_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__352_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__353_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__354_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__355_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__356_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__346_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__347_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__348_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__349_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__342_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__343_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__344_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__345_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__335_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__336_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__337_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__338_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__339_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__340_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__341_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__330_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__331_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__332_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__333_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__321_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__322_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__323_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__324_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__325_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__326_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__327_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__314_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__315_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__316_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__318_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__319_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__320_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__307_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__308_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__309_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__310_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__311_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__312_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__313_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__300_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__301_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__303_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__305_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__293_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__294_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__295_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__299_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__290_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__291_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__285_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__288_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__278_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__279_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__281_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__272_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__274_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__276_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__277_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__264_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__265_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__266_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__267_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__268_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__269_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__270_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__257_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__258_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__259_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__246_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__247_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__248_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__249_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__236_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__237_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__238_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__239_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__240_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__241_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__242_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__232_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__233_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__234_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__235_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__228_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__229_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__230_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__231_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__221_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__222_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__223_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__224_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__225_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__226_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__227_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__214_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__215_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__216_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__217_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__218_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__219_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__220_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__207_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__208_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__209_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__210_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__211_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__212_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__213_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__200_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__201_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__202_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__203_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__204_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__205_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__206_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__193_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__194_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__195_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__196_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__197_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__198_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__199_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__186_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__187_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__188_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__189_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__190_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__191_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__192_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__179_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__180_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__181_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__182_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__183_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__184_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__185_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__175_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__176_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__177_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__178_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__171_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__172_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__173_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__174_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__164_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__165_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__166_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__167_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__168_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__169_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__170_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__157_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__158_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__159_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__160_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__161_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__162_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__163_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__150_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__151_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__152_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__153_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__154_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__155_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__156_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__143_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__144_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__145_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__146_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__147_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__148_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__149_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__136_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__137_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__138_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__139_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__140_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__141_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__142_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__129_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__130_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__132_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__133_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__134_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__135_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__122_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__123_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__124_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__125_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__126_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__127_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__128_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__118_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__119_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__120_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__121_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__114_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__115_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__116_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__117_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__107_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__108_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__109_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__110_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__111_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__112_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__113_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__100_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__101_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__102_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__103_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__104_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__105_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__106_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__93_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__94_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__95_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__96_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__97_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__98_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__99_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__86_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__87_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__88_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__89_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__90_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__91_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__92_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__79_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__80_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__81_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__82_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__83_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__84_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__85_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__72_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__73_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__74_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__75_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__76_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__77_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__78_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__65_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__66_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__67_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__68_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__69_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__70_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__71_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__61_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__62_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__63_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__64_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__57_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__58_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__59_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__60_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__50_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__51_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__52_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__53_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__54_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__55_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__56_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__43_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__44_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__45_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__46_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__47_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__48_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__49_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__36_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__37_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__38_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__39_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__40_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__41_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__42_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__29_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__30_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__31_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__32_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__33_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__34_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__35_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__22_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__23_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__24_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__25_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__27_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__28_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__18_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__20_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__21_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__14_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_leanImportsFromRust___closed__911: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__911_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_leanImportsFromRust: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__911_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__1_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 115, 116, 114, 101, 97, 109, 95, 111, 102, 95, 104, 97, 110, 100,
        108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__2_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115, 95,
        103, 101, 116, 95, 114, 117, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__3_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115, 95,
        109, 107, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__4_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115, 95,
        112, 114, 111, 99, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__5_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 115, 101, 116, 95, 114, 101, 100, 117, 99, 105, 98, 105, 108, 105,
        116, 121, 95, 115, 116, 97, 116, 117, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__6_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__7_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115, 95,
        103, 101, 116, 95, 110, 117, 109, 95, 116, 104, 114, 101, 97, 100, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__8_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 115, 104, 101, 108, 108, 95, 111, 112, 116, 105, 111, 110, 115, 95,
        103, 101, 116, 95, 112, 114, 111, 102, 105, 108, 101, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__9_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__10_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        108, 101, 97, 110, 95, 114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 95, 104,
        105, 110, 116, 115, 95, 103, 101, 116, 95, 104, 101, 105, 103, 104, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__11_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 114, 101, 103, 105, 115, 116, 101, 114, 95, 111, 112, 116, 105, 111,
        110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__12_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 112, 114, 105, 118, 97, 116, 101, 95, 116, 111, 95, 117, 115, 101,
        114, 95, 110, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__13_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 95, 105, 110, 102,
        111, 95, 102, 114, 111, 109, 95, 99, 108, 97, 115, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__14_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__15_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 114, 101, 99, 117, 114, 115, 111, 114, 95, 105, 115, 95, 117, 110,
        115, 97, 102, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__16_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 111, 112, 116, 105, 111, 110, 115, 95, 117, 112, 100, 97, 116, 101,
        95, 98, 111, 111, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__17_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 112, 114, 105, 118, 97, 116, 101, 95, 112, 114, 101, 102, 105, 120,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__18_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 97, 112, 112, 101, 110, 100, 95, 105, 110,
        100, 101, 120, 95, 97, 102, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__19_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 104, 97, 115, 104, 95, 101, 120, 112, 111,
        114, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__20_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 109, 107, 95, 110, 117, 109, 101, 114, 97,
        108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__21_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 110, 97, 109, 101, 95, 109, 107, 95, 115, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__22_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__23_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 111, 112, 116, 105, 111, 110, 115, 95, 103, 101, 116, 95, 98, 111,
        111, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__24_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 111, 112, 116, 105, 111, 110, 115, 95, 103, 101, 116, 95, 101, 109,
        112, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__25_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 115, 121, 110, 116, 97, 120, 95, 105, 100, 101, 110,
        116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__26_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 116, 104, 101, 111, 114, 101, 109, 95, 118, 97, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__27_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__28_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__29_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 95,
        105, 110, 102, 111, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__30_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__31_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 114, 101, 99, 117, 114, 115, 111, 114, 95, 118, 97,
        108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__32_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116,
        121, 95, 104, 105, 110, 116, 115, 95, 114, 101, 103, 117, 108, 97, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__33_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__34_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 109, 97, 110, 103, 108, 101, 100, 95, 98, 111, 120,
        101, 100, 95, 110, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__35_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__36_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__36:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__37_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 117, 110,
        115, 97, 116, 105, 115, 102, 105, 101, 100, 95, 99, 111, 110, 115, 116, 114, 97, 105, 110,
        116, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__37:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__38_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 117, 110,
        115, 117, 112, 112, 111, 114, 116, 101, 100, 95, 111, 112, 101, 114, 97, 116, 105, 111,
        110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__38:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__39_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 117, 115, 101, 114, 95, 101, 114, 114,
        111, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__39:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__40_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__40:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__41_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 114, 101,
        115, 111, 117, 114, 99, 101, 95, 101, 120, 104, 97, 117, 115, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__41:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__42_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 114, 101,
        115, 111, 117, 114, 99, 101, 95, 101, 120, 104, 97, 117, 115, 116, 101, 100, 95, 102, 105,
        108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__42:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__43_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 114, 101,
        115, 111, 117, 114, 99, 101, 95, 118, 97, 110, 105, 115, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__43:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__44_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 116, 105,
        109, 101, 95, 101, 120, 112, 105, 114, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__44:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__45_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 112, 101,
        114, 109, 105, 115, 115, 105, 111, 110, 95, 100, 101, 110, 105, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__45:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__46_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 112, 101,
        114, 109, 105, 115, 115, 105, 111, 110, 95, 100, 101, 110, 105, 101, 100, 95, 102, 105,
        108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__46:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__46_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__47_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 112, 114,
        111, 116, 111, 99, 111, 108, 95, 101, 114, 114, 111, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__47:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__48_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 114, 101,
        115, 111, 117, 114, 99, 101, 95, 98, 117, 115, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__48:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__49_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105, 110,
        116, 101, 114, 114, 117, 112, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__49:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__50_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105, 110,
        118, 97, 108, 105, 100, 95, 97, 114, 103, 117, 109, 101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__50:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__50_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__51_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105, 110,
        118, 97, 108, 105, 100, 95, 97, 114, 103, 117, 109, 101, 110, 116, 95, 102, 105, 108, 101,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__51:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__51_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__52_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 110, 111,
        95, 102, 105, 108, 101, 95, 111, 114, 95, 100, 105, 114, 101, 99, 116, 111, 114, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__52:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__53_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 110, 111,
        95, 115, 117, 99, 104, 95, 116, 104, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__53:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__54_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 110, 111,
        95, 115, 117, 99, 104, 95, 116, 104, 105, 110, 103, 95, 102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__54:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__55_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 111, 116,
        104, 101, 114, 95, 101, 114, 114, 111, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__55:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__56_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 104, 97,
        114, 100, 119, 97, 114, 101, 95, 102, 97, 117, 108, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__56:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__57_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105, 108,
        108, 101, 103, 97, 108, 95, 111, 112, 101, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__57:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__57_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__58_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105, 110,
        97, 112, 112, 114, 111, 112, 114, 105, 97, 116, 101, 95, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__58:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__58_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__59_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 105, 110,
        97, 112, 112, 114, 111, 112, 114, 105, 97, 116, 101, 95, 116, 121, 112, 101, 95, 102, 105,
        108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__59:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__60_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 118,
        97, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__60:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__60_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__61_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 97, 108,
        114, 101, 97, 100, 121, 95, 101, 120, 105, 115, 116, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__61:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__61_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__62_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 97, 108,
        114, 101, 97, 100, 121, 95, 101, 120, 105, 115, 116, 115, 95, 102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__62:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__62_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__63_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 101, 111,
        102, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__63:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__64_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__64:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__65_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 98, 111, 111, 108, 95, 100, 97, 116, 97, 95, 118, 97,
        108, 117, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__65:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__65_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__66_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114,
        95, 118, 97, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__66:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__66_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__67_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 95,
        118, 97, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__67:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__67_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__68_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 101, 110, 118, 105, 114,
        111, 110, 109, 101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__68:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__68_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__69_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 101, 109, 112, 116, 121, 95, 108, 111, 99, 97, 108,
        95, 99, 116, 120, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__69:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__69_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__70_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 101, 97, 110, 95, 109, 107, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 100,
        101, 99, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__70:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__70_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__71_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 110, 117, 109, 95, 105,
        110, 100, 105, 99, 101, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__71:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__71_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__72_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 100, 101, 99, 108, 95, 98, 105, 110, 100,
        101, 114, 95, 105, 110, 102, 111, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__72:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__72_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__73_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 102, 105, 110, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__73:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__73_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__74_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 105, 115, 95, 101, 109,
        112, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__74:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__74_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__75_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 109, 107, 95, 108, 101,
        116, 95, 100, 101, 99, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__75:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__75_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__76_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 109, 107, 95, 108, 111,
        99, 97, 108, 95, 100, 101, 99, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__76:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__76_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__77_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__77:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__77_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__78_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__78:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__78_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__79_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__79:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__79_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__80_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__80:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__80_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__81_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__81:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__81_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__82_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__82:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__82_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__83_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 108, 111, 99, 97, 108, 95, 99, 116, 120, 95, 101, 114, 97, 115, 101,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__83:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__83_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__84_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__84:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__84_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__85_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__85:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__85_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__86_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__86:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__86_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__87_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 109, 107, 95, 112, 97, 114, 97, 109, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__87:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__87_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__88_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__88:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__88_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__89_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 108, 101, 118, 101, 108, 95, 104, 97, 115, 95, 109, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__89:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__89_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__90_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__90:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__90_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__91_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__91:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__91_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__92_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 100, 105, 97, 103, 95, 105, 115,
        95, 101, 110, 97, 98, 108, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__92:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__92_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__93_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 103, 101, 116, 95, 100, 105, 97,
        103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__93:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__93_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__94_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 114, 101, 99, 111, 114, 100, 95,
        117, 110, 102, 111, 108, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__94:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__94_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__95_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 107, 101, 114, 110, 101, 108, 95, 115, 101, 116, 95, 100, 105, 97,
        103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__95:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__95_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__96_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 95, 112, 114, 105, 118, 97, 116, 101, 95, 110, 97, 109,
        101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__96:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__96_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__97_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 95, 116, 114, 97, 99, 101, 95, 99, 108, 97, 115, 115, 95,
        101, 110, 97, 98, 108, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__97:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__97_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__98_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 105, 115, 95, 117, 110, 115, 97, 102, 101, 95, 105, 110, 100, 117,
        99, 116, 105, 118, 101, 95, 100, 101, 99, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__98:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__98_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__99_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__99:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__99_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__100_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__100:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__100_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__101_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__101:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__101_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__102_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__102:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__102_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__103_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__103:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__103_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__104_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__104:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__104_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__105_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__105:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__105_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__106_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__106:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__106_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__107_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 105, 111, 95, 101, 114, 114, 111, 114, 95, 116, 111, 95, 115, 116,
        114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__107:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__107_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__108_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__108:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__108_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__109_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 105, 114, 95, 102, 105, 110, 100, 95, 101, 110, 118, 95, 100, 101,
        99, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__109:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__109_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__110_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 105, 114, 95, 102, 105, 110, 100, 95, 101, 110, 118, 95, 100, 101,
        99, 108, 95, 98, 111, 120, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__110:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__110_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__111_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 118, 97, 108, 95,
        105, 115, 95, 117, 110, 115, 97, 102, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__111:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__111_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__112_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__112:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__112_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__113_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__113:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__113_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__114_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 104, 97, 115, 95, 111, 117, 116, 95, 112, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__114:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__114_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__115_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 118, 97, 108, 95,
        105, 115, 95, 114, 101, 99, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__115:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__115_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__116_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 118, 97, 108, 95,
        105, 115, 95, 114, 101, 102, 108, 101, 120, 105, 118, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__116:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__116_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__117_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 104, 97, 115, 95, 109, 97, 116, 99, 104, 95, 112, 97, 116, 116, 101,
        114, 110, 95, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__117:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__117_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__118_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 114, 101, 100, 117, 99, 105, 98, 105, 108, 105,
        116, 121, 95, 115, 116, 97, 116, 117, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__118:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__118_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__119_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 114, 101, 103, 117, 108, 97, 114, 95, 105, 110,
        105, 116, 95, 102, 110, 95, 110, 97, 109, 101, 95, 102, 111, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__119:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__119_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__120_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 115, 121, 109, 98, 111, 108, 95, 115, 116, 101,
        109, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__120:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__120_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__121_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 108, 109, 118, 97, 114, 95, 97, 115, 115, 105,
        103, 110, 109, 101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__121:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__121_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__122_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 109, 118, 97, 114, 95, 97, 115, 115, 105, 103,
        110, 109, 101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__122:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__122_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__123_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 111, 112, 116, 105, 111, 110, 95, 100, 101, 99,
        108, 115, 95, 97, 114, 114, 97, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__123:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__123_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__124_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__124:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__124_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__125_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 112, 114, 111, 102, 105, 108, 101, 114, 95, 116,
        104, 114, 101, 115, 104, 111, 108, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__125:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__125_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__126_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 100, 101, 108, 97, 121, 101, 100, 95, 109, 118,
        97, 114, 95, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__126:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__126_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__127_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 101, 120, 112, 111, 114, 116, 95, 110, 97, 109,
        101, 95, 102, 111, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__127:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__127_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__128_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 103, 101, 116, 95, 105, 110, 105, 116, 95, 102, 110, 95, 110, 97,
        109, 101, 95, 102, 111, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__128:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__128_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__129_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__129:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__129_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__130_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__130:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__130_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__131_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 102, 108, 111, 97, 116, 51, 50, 95, 111, 102, 95, 110, 97, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__131:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__131_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__132_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__132:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__132_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__133_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__133:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__133_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__134_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__134:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__134_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__135_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__135:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__135_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__136_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 102, 111, 114, 97, 108, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__136:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__136_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__137_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__137:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__137_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__138_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 109, 107, 95, 108, 97, 109, 98, 100, 97, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__138:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__138_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__139_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__139:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__139_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__140_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 108, 111, 111, 115, 101, 95, 98, 118, 97,
        114, 95, 114, 97, 110, 103, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__140:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__140_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__141_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__141:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__141_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__142_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__142:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__142_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__143_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__143:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__143_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__144_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 108, 101, 118, 101, 108,
        95, 112, 97, 114, 97, 109, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__144:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__144_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__145_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__145:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__145_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__146_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__146:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__146_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__147_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__147:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__147_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__148_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 98, 105, 110, 100, 101, 114, 95, 105, 110,
        102, 111, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__148:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__148_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__149_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 99, 111, 110, 115, 117, 109, 101, 95, 116,
        121, 112, 101, 95, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__149:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__149_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__150_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 101, 120, 112, 114, 95,
        109, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__150:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__150_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__151_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__151:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__151_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__152_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        108, 101, 97, 110, 95, 101, 120, 112, 114, 95, 104, 97, 115, 95, 108, 101, 118, 101, 108,
        95, 109, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__152:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__152_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__153_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 102, 114,
        101, 101, 95, 114, 101, 103, 105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__153:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__153_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__154_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 109, 97,
        114, 107, 95, 113, 117, 111, 116, 95, 105, 110, 105, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__154:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__154_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__155_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 113, 117,
        111, 116, 95, 105, 110, 105, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__155:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__155_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__156_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 101, 114, 97, 115, 101, 95, 109, 97, 99, 114, 111, 95, 115, 99, 111,
        112, 101, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__156:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__156_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__157_value:
    crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        108, 101, 97, 110, 95, 101, 108, 97, 98, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101,
        110, 116, 95, 117, 112, 100, 97, 116, 101, 95, 98, 97, 115, 101, 95, 97, 102, 116, 101,
        114, 95, 107, 101, 114, 110, 101, 108, 95, 97, 100, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__157:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__157_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__158_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        108, 101, 97, 110, 95, 101, 110, 97, 98, 108, 101, 95, 105, 110, 105, 116, 105, 97, 108,
        105, 122, 101, 114, 95, 101, 120, 101, 99, 117, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__158:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__158_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__159_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 97, 100,
        100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__159:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__159_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__160_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        108, 101, 97, 110, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 95, 102, 105,
        110, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__160:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__160_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__161_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 95, 118, 97, 108,
        95, 103, 101, 116, 95, 115, 97, 102, 101, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__161:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__161_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__162_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__162:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__162_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__163_value:
    crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
        115, 115, 105, 103, 110, 109, 101, 110, 116, 95, 109, 118, 97, 114, 95, 105, 100, 95, 112,
        101, 110, 100, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__163:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__163_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__164_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        108, 101, 97, 110, 95, 100, 101, 109, 97, 110, 103, 108, 101, 95, 98, 116, 95, 108, 105,
        110, 101, 95, 99, 115, 116, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__164:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__164_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__165_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 101, 108, 97, 98, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101,
        110, 116, 95, 111, 102, 95, 107, 101, 114, 110, 101, 108, 95, 101, 110, 118, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__165:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__165_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__166_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        108, 101, 97, 110, 95, 101, 108, 97, 98, 95, 101, 110, 118, 105, 114, 111, 110, 109, 101,
        110, 116, 95, 116, 111, 95, 107, 101, 114, 110, 101, 108, 95, 101, 110, 118, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__166:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__166_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__167_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        108, 101, 97, 110, 95, 100, 97, 116, 97, 95, 118, 97, 108, 117, 101, 95, 98, 101, 113, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__167:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__167_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__168_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 95, 100, 97, 116, 97, 95, 118, 97, 108, 117, 101, 95, 98, 111, 111, 108,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__168:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__168_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__169_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        108, 101, 97, 110, 95, 100, 97, 116, 97, 95, 118, 97, 108, 117, 101, 95, 116, 111, 95, 115,
        116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__169:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__169_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__170_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        108, 101, 97, 110, 95, 100, 101, 99, 108, 95, 103, 101, 116, 95, 115, 111, 114, 114, 121,
        95, 100, 101, 112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__170:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__170_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__171_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        108, 101, 97, 110, 95, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 95, 118, 97,
        108, 95, 105, 115, 95, 117, 110, 115, 97, 102, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__171:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__171_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__172_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__172:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__172_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__173_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__173:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__173_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__174_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__174:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__174_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__175_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__175:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__175_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__176_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        108, 101, 97, 110, 95, 97, 116, 116, 114, 105, 98, 117, 116, 101, 95, 97, 112, 112, 108,
        105, 99, 97, 116, 105, 111, 110, 95, 116, 105, 109, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__176:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__176_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__177_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__177:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__177_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__178_value:
    crate::leanh::LeanArrayObject<245> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 245) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 245,
    m_capacity: 245,
    m_data: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__878_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__172_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__173_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__174_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__175_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__176_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__177_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__837_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__171_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__831_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__832_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__167_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__168_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__169_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__170_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__161_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__162_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__163_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__164_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__825_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__165_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__166_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__157_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__158_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__159_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__160_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__153_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__154_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__155_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__156_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__818_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__807_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__148_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__149_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__150_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__151_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__152_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__144_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__145_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__146_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__147_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__140_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__141_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__142_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__143_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__136_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__137_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__138_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__139_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__132_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__133_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__134_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__135_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__129_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__130_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__131_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__720_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__126_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__127_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__128_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__724_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__121_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__714_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__122_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__718_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__123_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__124_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__125_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__118_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__119_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__711_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__120_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__700_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__701_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__702_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__703_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__704_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__705_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__692_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__693_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__694_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__695_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__117_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__114_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__696_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__115_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__116_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__111_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__697_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__112_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__113_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__105_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__106_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__107_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__108_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__480_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__109_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__110_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__102_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__103_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__104_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__482_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__99_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__483_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__100_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__101_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__96_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__484_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__97_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__98_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__92_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__93_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__94_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__95_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__88_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__89_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__90_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__91_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__84_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__85_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__86_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__87_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__77_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__78_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__79_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__80_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__81_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__82_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__83_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__73_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__74_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__75_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__76_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__71_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__72_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__370_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__357_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__64_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__65_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__66_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__67_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__68_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__69_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__70_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__60_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__61_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__62_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__63_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__56_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__57_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__58_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__59_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__49_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__50_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__51_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__52_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__53_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__54_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__55_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__45_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__46_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__47_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__48_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__41_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__42_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__43_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__44_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__37_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__38_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__39_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__40_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__33_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__34_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__35_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__36_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__29_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__30_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__31_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__32_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__25_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__26_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__27_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__28_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__18_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__20_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__21_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__22_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__23_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__24_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__328_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__329_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__14_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__334_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__317_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__302_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__304_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__306_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__296_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__297_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__298_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__289_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__292_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__286_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__287_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__280_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__282_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__283_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__284_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__271_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__273_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__275_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__260_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__261_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__262_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__263_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__250_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__251_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__252_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__253_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__254_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__255_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__256_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__243_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__244_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__245_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__131_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_leanImportsFromRust___closed__26_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__178:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__178_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_rustShouldImportFromLean: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_rustShouldImportFromLean___closed__178_value)
        as *mut crate::leanh::LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_EmitRust_LeanhGenerated(builtin);
}
