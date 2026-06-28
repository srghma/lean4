// Lean compiler output
// Module: Init.Guard
// Imports: Init.Conv
use crate::r#gen::Init::Conv::{initialize_Init_Conv, runtime_initialize_Init_Conv};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub static l_Lean_Parser_colonR___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 108, 111, 110, 82, 0],
};
static mut l_Lean_Parser_colonR___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonR___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_colonR___closed__1_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Parser_colonR___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colonR___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Parser_colonR___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_colonR___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colonR___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colonR___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__0_value) as *mut LeanObject,
        11766820169793439539 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonR___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonR___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colonR___closed__4_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Lean_Parser_colonR___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonR___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colonR___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_colonR___closed__4_value) as *mut LeanObject],
};
static mut l_Lean_Parser_colonR___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonR___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_colonR___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonR___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonR___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colonR: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonR___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_colonD___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 108, 111, 110, 68, 0],
};
static mut l_Lean_Parser_colonD___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonD___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_colonD___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colonD___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonD___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colonD___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonD___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonD___closed__0_value) as *mut LeanObject,
        4334716130055557871 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonD___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonD___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colonD___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 126, 32, 0],
};
static mut l_Lean_Parser_colonD___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonD___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_colonD___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_colonD___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_colonD___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonD___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colonD___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonD___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonD___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonD___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonD___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonD___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colonD: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonD___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colonS___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 108, 111, 110, 83, 0],
};
static mut l_Lean_Parser_colonS___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonS___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_colonS___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colonS___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonS___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colonS___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonS___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonS___closed__0_value) as *mut LeanObject,
        16142497725452366017 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonS___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonS___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colonS___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 4,
    m_data: [32, 58, 226, 130, 155, 32, 0],
};
static mut l_Lean_Parser_colonS___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonS___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_colonS___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_colonS___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_colonS___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonS___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colonS___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonS___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonS___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonS___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonS___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonS___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colonS: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonS___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colonA___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 108, 111, 110, 65, 0],
};
static mut l_Lean_Parser_colonA___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonA___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_colonA___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colonA___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonA___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colonA___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonA___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonA___closed__0_value) as *mut LeanObject,
        2800469225767172270 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonA___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonA___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colonA___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 4,
    m_data: [32, 58, 226, 130, 144, 32, 0],
};
static mut l_Lean_Parser_colonA___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonA___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_colonA___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_colonA___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_colonA___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonA___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colonA___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonA___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonA___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonA___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonA___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonA___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colonA: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonA___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colon___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 108, 111, 110, 0],
};
static mut l_Lean_Parser_colon___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colon___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_colon___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colon___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colon___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__0_value) as *mut LeanObject,
        16701333901772390046 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colon___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colon___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colon___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Parser_colon___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colon___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_colon___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__2_value) as *mut LeanObject,
        393173242845875278 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colon___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colon___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonS___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonA___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colon___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colon___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colon___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonD___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colon___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colon___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_colon___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colon___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colon___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_colon___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colon___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colon___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colon: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colon___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqR___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 108, 111, 110, 69, 113, 82, 0],
};
static mut l_Lean_Parser_colonEqR___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_colonEqR___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colonEqR___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colonEqR___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__0_value) as *mut LeanObject,
        4547212498149662503 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEqR___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqR___closed__2_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Parser_colonEqR___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqR___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_colonEqR___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqR___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEqR___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colonEqR: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqD___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 108, 111, 110, 69, 113, 68, 0],
};
static mut l_Lean_Parser_colonEqD___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_colonEqD___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colonEqD___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colonEqD___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__0_value) as *mut LeanObject,
        9469198591938552093 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEqD___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqD___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 58, 61, 126, 32, 0],
};
static mut l_Lean_Parser_colonEqD___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqD___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_colonEqD___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqD___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEqD___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colonEqD: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqS___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 108, 111, 110, 69, 113, 83, 0],
};
static mut l_Lean_Parser_colonEqS___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_colonEqS___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colonEqS___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colonEqS___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__0_value) as *mut LeanObject,
        18100060585123032661 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEqS___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqS___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 5,
    m_data: [32, 58, 61, 226, 130, 155, 32, 0],
};
static mut l_Lean_Parser_colonEqS___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqS___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_colonEqS___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqS___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEqS___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colonEqS: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqA___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 108, 111, 110, 69, 113, 65, 0],
};
static mut l_Lean_Parser_colonEqA___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_colonEqA___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colonEqA___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colonEqA___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__0_value) as *mut LeanObject,
        398647838421166144 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEqA___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqA___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 5,
    m_data: [32, 58, 61, 226, 130, 144, 32, 0],
};
static mut l_Lean_Parser_colonEqA___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqA___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_colonEqA___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEqA___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEqA___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colonEqA: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEq___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 108, 111, 110, 69, 113, 0],
};
static mut l_Lean_Parser_colonEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_colonEq___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_colonEq___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_colonEq___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__0_value) as *mut LeanObject,
        3454211822294123381 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEq___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqS___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqA___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEq___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEq___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqD___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEq___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEqR___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEq___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_colonEq___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_colonEq___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_colonEq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_equalR___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 117, 97, 108, 82, 0],
};
static mut l_Lean_Parser_equalR___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalR___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_equalR___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_equalR___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalR___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_equalR___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalR___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalR___closed__0_value) as *mut LeanObject,
        17078963301316888828 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equalR___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalR___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_equalR___closed__2_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Lean_Parser_equalR___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalR___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_equalR___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_equalR___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_equalR___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalR___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_equalR___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalR___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalR___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalR___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equalR___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalR___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_equalR: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalR___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_equalD___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 117, 97, 108, 68, 0],
};
static mut l_Lean_Parser_equalD___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalD___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_equalD___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_equalD___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalD___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_equalD___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalD___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalD___closed__0_value) as *mut LeanObject,
        9006235547594326259 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equalD___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalD___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_equalD___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 61, 126, 32, 0],
};
static mut l_Lean_Parser_equalD___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalD___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_equalD___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_equalD___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_equalD___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalD___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_equalD___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalD___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalD___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalD___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equalD___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalD___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_equalD: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalD___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_equalS___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 117, 97, 108, 83, 0],
};
static mut l_Lean_Parser_equalS___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalS___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_equalS___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_equalS___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalS___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_equalS___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalS___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalS___closed__0_value) as *mut LeanObject,
        13788227380297645704 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equalS___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalS___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_equalS___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 4,
    m_data: [32, 61, 226, 130, 155, 32, 0],
};
static mut l_Lean_Parser_equalS___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalS___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_equalS___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_equalS___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_equalS___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalS___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_equalS___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalS___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalS___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalS___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equalS___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalS___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_equalS: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalS___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_equalA___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 117, 97, 108, 65, 0],
};
static mut l_Lean_Parser_equalA___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalA___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_equalA___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_equalA___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalA___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_equalA___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalA___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalA___closed__0_value) as *mut LeanObject,
        8682205543839346023 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equalA___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalA___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_equalA___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 4,
    m_data: [32, 61, 226, 130, 144, 32, 0],
};
static mut l_Lean_Parser_equalA___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalA___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_equalA___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_equalA___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Parser_equalA___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalA___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_equalA___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equalA___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalA___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalA___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equalA___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalA___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_equalA: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equalA___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_equal___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 113, 117, 97, 108, 0],
};
static mut l_Lean_Parser_equal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equal___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_equal___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_equal___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_equal___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__0_value) as *mut LeanObject,
        17604351797772570779 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equal___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equal___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_equal___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalS___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalA___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equal___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equal___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_equal___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalD___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equal___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equal___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_equal___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equalR___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equal___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equal___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_equal___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_equal___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equal___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_equal: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_equal___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__0_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_guardExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__1_value: LeanStringObject<10> =
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
        m_data: [103, 117, 97, 114, 100, 69, 120, 112, 114, 0],
    };
static mut l_Lean_Parser_Tactic_guardExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__1_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_guardExpr___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_guardExpr___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_guardExpr___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__2_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__0_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_guardExpr___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__2_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__1_value) as *mut LeanObject,
        2406710036554907729 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__3_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Tactic_guardExpr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__3_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__5_value: LeanStringObject<12> =
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
        m_data: [103, 117, 97, 114, 100, 95, 101, 120, 112, 114, 32, 0],
    };
static mut l_Lean_Parser_Tactic_guardExpr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__5_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__7_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_guardExpr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__7_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__8_value) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__12_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__8_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExpr___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__2_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardExpr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__14_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_guardExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExprConv___closed__0_value: LeanStringObject<14> =
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
            103, 117, 97, 114, 100, 69, 120, 112, 114, 67, 111, 110, 118, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_guardExprConv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExprConv___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_guardExprConv___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_guardExprConv___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExprConv___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_guardExprConv___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExprConv___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_guardExprConv___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExprConv___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExprConv___closed__0_value)
                as *mut LeanObject,
            17520459286155217955 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_guardExprConv___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExprConv___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardExprConv___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExprConv___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_guardExprConv___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExprConv___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_guardExprConv: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExprConv___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardTarget___closed__0_value: LeanStringObject<12> =
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
        m_data: [103, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 0],
    };
static mut l_Lean_Parser_Tactic_guardTarget___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_guardTarget___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_guardTarget___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_guardTarget___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_guardTarget___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__0_value) as *mut LeanObject,
        9705855369448785090 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardTarget___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardTarget___closed__2_value: LeanStringObject<14> =
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
            103, 117, 97, 114, 100, 95, 116, 97, 114, 103, 101, 116, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_guardTarget___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardTarget___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardTarget___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardTarget___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_equal___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardTarget___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardTarget___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardTarget___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardTarget___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardTarget___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_guardTarget: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardTargetConv___closed__0_value: LeanStringObject<16> =
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
            103, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 67, 111, 110, 118, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_guardTargetConv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTargetConv___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_guardTargetConv___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_guardTargetConv___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTargetConv___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_guardTargetConv___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTargetConv___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_guardTargetConv___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTargetConv___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTargetConv___closed__0_value)
                as *mut LeanObject,
            1133233218418288393 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_guardTargetConv___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTargetConv___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardTargetConv___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTargetConv___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTarget___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_guardTargetConv___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTargetConv___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_guardTargetConv: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardTargetConv___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__0_value: LeanStringObject<9> =
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
        m_data: [103, 117, 97, 114, 100, 72, 121, 112, 0],
    };
static mut l_Lean_Parser_Tactic_guardHyp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_guardHyp___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_guardHyp___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_guardHyp___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__0_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_guardHyp___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__0_value) as *mut LeanObject,
        12801252452760768259 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__2_value: LeanStringObject<11> =
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
        m_data: [103, 117, 97, 114, 100, 95, 104, 121, 112, 32, 0],
    };
static mut l_Lean_Parser_Tactic_guardHyp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__8_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__6_value: LeanStringObject<9> =
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
static mut l_Lean_Parser_Tactic_guardHyp___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__6_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colon___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonEq___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__12_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHyp___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_guardHyp___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__14_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_guardHyp: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHypConv___closed__0_value: LeanStringObject<13> =
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
        m_data: [103, 117, 97, 114, 100, 72, 121, 112, 67, 111, 110, 118, 0],
    };
static mut l_Lean_Parser_Tactic_guardHypConv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHypConv___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_guardHypConv___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_guardHypConv___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHypConv___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_guardHypConv___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHypConv___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_guardHypConv___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHypConv___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHypConv___closed__0_value)
                as *mut LeanObject,
            9950005495765075193 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_guardHypConv___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHypConv___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_guardHypConv___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHypConv___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHyp___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_guardHypConv___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHypConv___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_guardHypConv: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_guardHypConv___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardExprCmd___closed__0_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Command_guardExprCmd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardExprCmd___closed__1_value: LeanStringObject<13> =
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
        m_data: [103, 117, 97, 114, 100, 69, 120, 112, 114, 67, 109, 100, 0],
    };
static mut l_Lean_Parser_Command_guardExprCmd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__1_value) as *mut LeanObject;
static l_Lean_Parser_Command_guardExprCmd___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_guardExprCmd___closed__2_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_guardExprCmd___closed__2_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_guardExprCmd___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__1_value)
                as *mut LeanObject,
            2836449611787596701 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_guardExprCmd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardExprCmd___closed__3_value: LeanStringObject<13> =
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
        m_data: [35, 103, 117, 97, 114, 100, 95, 101, 120, 112, 114, 32, 0],
    };
static mut l_Lean_Parser_Command_guardExprCmd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardExprCmd___closed__4_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_guardExprCmd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardExprCmd___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_guardExprCmd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardExprCmd___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_equal___closed__5_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_guardExprCmd___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardExprCmd___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_guardExprCmd___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardExprCmd___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__2_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_guardExprCmd___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Command_guardExprCmd: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardCmd___closed__0_value: LeanStringObject<9> =
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
        m_data: [103, 117, 97, 114, 100, 67, 109, 100, 0],
    };
static mut l_Lean_Parser_Command_guardCmd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Command_guardCmd___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Command_guardCmd___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_colonR___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Command_guardCmd___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_guardExprCmd___closed__0_value)
            as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Command_guardCmd___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__0_value) as *mut LeanObject,
        8409249086422357623 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Command_guardCmd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardCmd___closed__2_value: LeanStringObject<8> =
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
        m_data: [35, 103, 117, 97, 114, 100, 32, 0],
    };
static mut l_Lean_Parser_Command_guardCmd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardCmd___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Command_guardCmd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardCmd___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_guardExpr___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Command_guardCmd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_guardCmd___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Command_guardCmd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Command_guardCmd: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_guardCmd___closed__5_value) as *mut LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Guard(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Conv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Guard(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Guard(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Conv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Guard(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Guard(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Guard(builtin);
}
