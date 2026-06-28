// Lean compiler output
// Module: Init.Grind.Lint
// Imports: Init.Tactics
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_configItem, runtime_initialize_Init_Tactics,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_unsigned_to_nat,
};
pub static l_Lean_Grind_grindLintCheck___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintCheck___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__1_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintCheck___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__2_value: LeanStringObject<15> = LeanStringObject {
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
        103, 114, 105, 110, 100, 76, 105, 110, 116, 67, 104, 101, 99, 107, 0,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__2_value) as *mut LeanObject;
static l_Lean_Grind_grindLintCheck___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Grind_grindLintCheck___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__1_value) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
pub static l_Lean_Grind_grindLintCheck___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__2_value) as *mut LeanObject,
        16879946614306402622 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__4_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintCheck___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__4_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__6_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [35, 103, 114, 105, 110, 100, 95, 108, 105, 110, 116, 0],
};
static mut l_Lean_Grind_grindLintCheck___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__6_value) as *mut LeanObject],
};
static mut l_Lean_Grind_grindLintCheck___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__8_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintCheck___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__8_value) as *mut LeanObject,
        17761616517784022991 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__9_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__10_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__9_value) as *mut LeanObject],
};
static mut l_Lean_Grind_grindLintCheck___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__10_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__11_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__12_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 104, 101, 99, 107, 0],
};
static mut l_Lean_Grind_grindLintCheck___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__12_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__12_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__13_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__14_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__15_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintCheck___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__15_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__15_value) as *mut LeanObject,
        2302572775315350313 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__16_value) as *mut LeanObject;
static mut l_Lean_Grind_grindLintCheck___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_grindLintCheck___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_grindLintCheck___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_grindLintCheck___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_grindLintCheck___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_grindLintCheck___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_grindLintCheck___closed__20_value: LeanStringObject<9> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintCheck___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__20_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__21_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__20_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__21_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__22_value: LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintCheck___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__22_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__23_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__22_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__23_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__24_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__24_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__25_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 111, 100, 117, 108, 101, 0],
};
static mut l_Lean_Grind_grindLintCheck___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__25_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__26_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__25_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__26_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__27_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__26_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__27_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__28_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__21_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__27_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__28_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__29_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__24_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__28_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__29_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__30_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintCheck___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__30_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__31_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__30_value) as *mut LeanObject,
        17243740965612849207 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__31_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__32_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintCheck___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__32_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__33_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__32_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__33_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__34_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__33_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__34_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__35_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__31_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__34_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__35_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__36_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__29_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__35_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__36_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintCheck___closed__37_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__21_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__36_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintCheck___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__37_value) as *mut LeanObject;
static mut l_Lean_Grind_grindLintCheck___closed__38_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_grindLintCheck___closed__38: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_grindLintCheck___closed__39_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_grindLintCheck___closed__39: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_grindLintCheck: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_grindLintInspect___closed__0_value: LeanStringObject<17> =
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
            103, 114, 105, 110, 100, 76, 105, 110, 116, 73, 110, 115, 112, 101, 99, 116, 0,
        ],
    };
static mut l_Lean_Grind_grindLintInspect___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__0_value) as *mut LeanObject;
static l_Lean_Grind_grindLintInspect___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Grind_grindLintInspect___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__1_value) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
pub static l_Lean_Grind_grindLintInspect___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__0_value) as *mut LeanObject,
        627953777420417167 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintInspect___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintInspect___closed__2_value: LeanStringObject<8> =
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
        m_data: [105, 110, 115, 112, 101, 99, 116, 0],
    };
static mut l_Lean_Grind_grindLintInspect___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintInspect___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintInspect___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintInspect___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintInspect___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintInspect___closed__4_value) as *mut LeanObject;
static mut l_Lean_Grind_grindLintInspect___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_grindLintInspect___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_grindLintInspect___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_grindLintInspect___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_grindLintInspect___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_grindLintInspect___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_grindLintInspect: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_grindLintMute___closed__0_value: LeanStringObject<14> = LeanStringObject {
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
        103, 114, 105, 110, 100, 76, 105, 110, 116, 77, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Grind_grindLintMute___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__0_value) as *mut LeanObject;
static l_Lean_Grind_grindLintMute___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Grind_grindLintMute___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__1_value) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
pub static l_Lean_Grind_grindLintMute___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__0_value) as *mut LeanObject,
        543388241676410444 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintMute___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintMute___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [109, 117, 116, 101, 0],
};
static mut l_Lean_Grind_grindLintMute___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintMute___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintMute___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintMute___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintMute___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintMute___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__35_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintMute___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintMute___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintMute___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Grind_grindLintMute: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintMute___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__0_value: LeanStringObject<14> = LeanStringObject {
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
        103, 114, 105, 110, 100, 76, 105, 110, 116, 83, 107, 105, 112, 0,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__0_value) as *mut LeanObject;
static l_Lean_Grind_grindLintSkip___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Grind_grindLintSkip___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__1_value) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
pub static l_Lean_Grind_grindLintSkip___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__0_value) as *mut LeanObject,
        949591075816843266 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__2_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Grind_grindLintSkip___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__5_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 117, 102, 102, 105, 120, 0],
};
static mut l_Lean_Grind_grindLintSkip___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__5_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__21_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__9_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintCheck___closed__35_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__10_value) as *mut LeanObject;
pub static l_Lean_Grind_grindLintSkip___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_grindLintSkip___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__11_value) as *mut LeanObject;
pub static mut l_Lean_Grind_grindLintSkip: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_grindLintSkip___closed__11_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Grind_grindLintCheck___closed__17() -> *mut LeanObject {
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    v___x_215_ = l_Lean_Parser_Tactic_configItem;
    v___x_216_ = l_Lean_Grind_grindLintCheck___closed__10;
    v___x_217_ = l_Lean_Grind_grindLintCheck___closed__5;
    v___x_218_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_218_, 0, v___x_217_);
    lean_ctor_set(v___x_218_, 1, v___x_216_);
    lean_ctor_set(v___x_218_, 2, v___x_215_);
    return v___x_218_;
}
pub unsafe fn _init_l_Lean_Grind_grindLintCheck___closed__18() -> *mut LeanObject {
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    v___x_219_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__17_once),
        _init_l_Lean_Grind_grindLintCheck___closed__17,
    );
    v___x_220_ = l_Lean_Grind_grindLintCheck___closed__16;
    v___x_221_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_221_, 0, v___x_220_);
    lean_ctor_set(v___x_221_, 1, v___x_219_);
    return v___x_221_;
}
pub unsafe fn _init_l_Lean_Grind_grindLintCheck___closed__19() -> *mut LeanObject {
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    v___x_222_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__18_once),
        _init_l_Lean_Grind_grindLintCheck___closed__18,
    );
    v___x_223_ = l_Lean_Grind_grindLintCheck___closed__14;
    v___x_224_ = l_Lean_Grind_grindLintCheck___closed__5;
    v___x_225_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_225_, 0, v___x_224_);
    lean_ctor_set(v___x_225_, 1, v___x_223_);
    lean_ctor_set(v___x_225_, 2, v___x_222_);
    return v___x_225_;
}
pub unsafe fn _init_l_Lean_Grind_grindLintCheck___closed__38() -> *mut LeanObject {
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v___x_269_ = l_Lean_Grind_grindLintCheck___closed__37;
    v___x_270_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__19_once),
        _init_l_Lean_Grind_grindLintCheck___closed__19,
    );
    v___x_271_ = l_Lean_Grind_grindLintCheck___closed__5;
    v___x_272_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_272_, 0, v___x_271_);
    lean_ctor_set(v___x_272_, 1, v___x_270_);
    lean_ctor_set(v___x_272_, 2, v___x_269_);
    return v___x_272_;
}
pub unsafe fn _init_l_Lean_Grind_grindLintCheck___closed__39() -> *mut LeanObject {
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    v___x_273_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__38_once),
        _init_l_Lean_Grind_grindLintCheck___closed__38,
    );
    v___x_274_ = lean_unsigned_to_nat(1022);
    v___x_275_ = l_Lean_Grind_grindLintCheck___closed__3;
    v___x_276_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_276_, 0, v___x_275_);
    lean_ctor_set(v___x_276_, 1, v___x_274_);
    lean_ctor_set(v___x_276_, 2, v___x_273_);
    return v___x_276_;
}
pub unsafe fn _init_l_Lean_Grind_grindLintCheck() -> *mut LeanObject {
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    v___x_277_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__39_once),
        _init_l_Lean_Grind_grindLintCheck___closed__39,
    );
    return v___x_277_;
}
pub unsafe fn _init_l_Lean_Grind_grindLintInspect___closed__5() -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintCheck___closed__18_once),
        _init_l_Lean_Grind_grindLintCheck___closed__18,
    );
    v___x_292_ = l_Lean_Grind_grindLintInspect___closed__4;
    v___x_293_ = l_Lean_Grind_grindLintCheck___closed__5;
    v___x_294_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_294_, 0, v___x_293_);
    lean_ctor_set(v___x_294_, 1, v___x_292_);
    lean_ctor_set(v___x_294_, 2, v___x_291_);
    return v___x_294_;
}
pub unsafe fn _init_l_Lean_Grind_grindLintInspect___closed__6() -> *mut LeanObject {
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v___x_295_ = l_Lean_Grind_grindLintCheck___closed__35;
    v___x_296_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintInspect___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintInspect___closed__5_once),
        _init_l_Lean_Grind_grindLintInspect___closed__5,
    );
    v___x_297_ = l_Lean_Grind_grindLintCheck___closed__5;
    v___x_298_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_298_, 0, v___x_297_);
    lean_ctor_set(v___x_298_, 1, v___x_296_);
    lean_ctor_set(v___x_298_, 2, v___x_295_);
    return v___x_298_;
}
pub unsafe fn _init_l_Lean_Grind_grindLintInspect___closed__7() -> *mut LeanObject {
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    v___x_299_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintInspect___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintInspect___closed__6_once),
        _init_l_Lean_Grind_grindLintInspect___closed__6,
    );
    v___x_300_ = lean_unsigned_to_nat(1022);
    v___x_301_ = l_Lean_Grind_grindLintInspect___closed__1;
    v___x_302_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_302_, 0, v___x_301_);
    lean_ctor_set(v___x_302_, 1, v___x_300_);
    lean_ctor_set(v___x_302_, 2, v___x_299_);
    return v___x_302_;
}
pub unsafe fn _init_l_Lean_Grind_grindLintInspect() -> *mut LeanObject {
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    v___x_303_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintInspect___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Grind_grindLintInspect___closed__7_once),
        _init_l_Lean_Grind_grindLintInspect___closed__7,
    );
    return v___x_303_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Lint(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn meta_initialize_Init_Grind_Lint(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Grind_grindLintCheck = _init_l_Lean_Grind_grindLintCheck();
    lean_mark_persistent(l_Lean_Grind_grindLintCheck);
    l_Lean_Grind_grindLintInspect = _init_l_Lean_Grind_grindLintInspect();
    lean_mark_persistent(l_Lean_Grind_grindLintInspect);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Lint(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Grind_Lint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Lint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Lint(builtin);
}
