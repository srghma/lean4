// Lean compiler output
// Module: Lake.DSL.Syntax
// Imports: Lake.DSL.DeclUtil
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4};
use crate::r#gen::Lake::DSL::DeclUtil::{
    initialize_Lake_DSL_DeclUtil, l_Lake_DSL_declValDo, l_Lake_DSL_identOrStr,
    l_Lake_DSL_optConfig, l_Lake_DSL_simpleBinder, runtime_initialize_Lake_DSL_DeclUtil,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_unsigned_to_nat,
};
pub static l_Lake_DSL_nameConst___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 97, 107, 101, 0],
};
static mut l_Lake_DSL_nameConst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject;
pub static l_Lake_DSL_nameConst___closed__1_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [68, 83, 76, 0],
};
static mut l_Lake_DSL_nameConst___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_nameConst___closed__2_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 97, 109, 101, 67, 111, 110, 115, 116, 0],
};
static mut l_Lake_DSL_nameConst___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__2_value) as *mut LeanObject;
static l_Lake_DSL_nameConst___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_nameConst___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_nameConst___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__2_value) as *mut LeanObject,
        12277407653222002017 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_nameConst___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_nameConst___closed__4_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 95, 110, 97, 109, 101, 95, 95, 0],
};
static mut l_Lake_DSL_nameConst___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_nameConst___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__4_value) as *mut LeanObject],
};
static mut l_Lake_DSL_nameConst___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_nameConst___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_nameConst___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__6_value) as *mut LeanObject;
pub static mut l_Lake_DSL_nameConst: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_dirConst___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 105, 114, 67, 111, 110, 115, 116, 0],
};
static mut l_Lake_DSL_dirConst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_dirConst___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_dirConst___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_dirConst___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__0_value) as *mut LeanObject,
        14737761738784435815 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_dirConst___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_dirConst___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [95, 95, 100, 105, 114, 95, 95, 0],
};
static mut l_Lake_DSL_dirConst___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_dirConst___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_dirConst___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_dirConst___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_dirConst___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_DSL_dirConst: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [103, 101, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lake_DSL_getConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_getConfig___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_getConfig___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_getConfig___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__0_value) as *mut LeanObject,
        6629962664469725265 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_getConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__2_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lake_DSL_getConfig___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_getConfig___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__4_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [103, 101, 116, 95, 99, 111, 110, 102, 105, 103, 63, 32, 0],
};
static mut l_Lake_DSL_getConfig___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__4_value) as *mut LeanObject],
};
static mut l_Lake_DSL_getConfig___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__6_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lake_DSL_getConfig___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__6_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_getConfig___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__7_value) as *mut LeanObject],
};
static mut l_Lake_DSL_getConfig___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_getConfig___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_getConfig___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_getConfig___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__10_value) as *mut LeanObject;
pub static mut l_Lake_DSL_getConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        112, 97, 99, 107, 97, 103, 101, 67, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lake_DSL_packageCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_packageCommand___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_packageCommand___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_packageCommand___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__0_value) as *mut LeanObject,
        3605886163266385533 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageCommand___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__2_value: LeanStringObject<9> = LeanStringObject {
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
static mut l_Lake_DSL_packageCommand___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__2_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageCommand___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__4_value: LeanStringObject<11> = LeanStringObject {
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
static mut l_Lake_DSL_packageCommand___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__4_value) as *mut LeanObject,
        3961966953292576997 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageCommand___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__5_value) as *mut LeanObject],
};
static mut l_Lake_DSL_packageCommand___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageCommand___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lake_DSL_packageCommand___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__9_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lake_DSL_packageCommand___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__10_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lake_DSL_packageCommand___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__11_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
};
static mut l_Lake_DSL_packageCommand___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__11_value) as *mut LeanObject;
static l_Lake_DSL_packageCommand___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lake_DSL_packageCommand___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lake_DSL_packageCommand___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__10_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_packageCommand___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__11_value) as *mut LeanObject,
        2533412339571800130 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageCommand___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__13_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 8,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value) as *mut LeanObject],
};
static mut l_Lake_DSL_packageCommand___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__13_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__14_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageCommand___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__14_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageCommand___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__16_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [112, 97, 99, 107, 97, 103, 101, 32, 0],
};
static mut l_Lake_DSL_packageCommand___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__16_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__17_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__16_value) as *mut LeanObject],
};
static mut l_Lake_DSL_packageCommand___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__17_value) as *mut LeanObject;
pub static l_Lake_DSL_packageCommand___closed__18_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__17_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageCommand___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__18_value) as *mut LeanObject;
static mut l_Lake_DSL_packageCommand___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_packageCommand___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_packageCommand___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_packageCommand___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_packageCommand___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_packageCommand___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_packageCommand___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_packageCommand___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_packageCommand: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_instCoePackageCommandCommand___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_DSL_instCoePackageCommandCommand___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_DSL_instCoePackageCommandCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lake_DSL_instCoePackageCommandCommand: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        112, 111, 115, 116, 85, 112, 100, 97, 116, 101, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_DSL_postUpdateDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_postUpdateDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_postUpdateDecl___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_postUpdateDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__0_value) as *mut LeanObject,
        7248721378401769890 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_postUpdateDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__2_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [112, 111, 115, 116, 95, 117, 112, 100, 97, 116, 101, 32, 0],
};
static mut l_Lake_DSL_postUpdateDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_postUpdateDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_postUpdateDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__5_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lake_DSL_postUpdateDecl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__5_value) as *mut LeanObject,
        17761616517784022991 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_postUpdateDecl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__6_value) as *mut LeanObject],
};
static mut l_Lake_DSL_postUpdateDecl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__7_value) as *mut LeanObject;
static mut l_Lake_DSL_postUpdateDecl___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_postUpdateDecl___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_postUpdateDecl___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_postUpdateDecl___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_postUpdateDecl___closed__11_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lake_DSL_postUpdateDecl___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__11_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__11_value) as *mut LeanObject,
        393173242845875278 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_postUpdateDecl___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__12_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__13_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lake_DSL_postUpdateDecl___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__13_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__14_value: LeanStringObject<14> = LeanStringObject {
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
        100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
    ],
};
static mut l_Lake_DSL_postUpdateDecl___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__14_value) as *mut LeanObject;
static l_Lake_DSL_postUpdateDecl___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lake_DSL_postUpdateDecl___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lake_DSL_postUpdateDecl___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__13_value) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_postUpdateDecl___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__14_value) as *mut LeanObject,
        13585030837571646948 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_postUpdateDecl___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value) as *mut LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__16_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 8,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value) as *mut LeanObject],
};
static mut l_Lake_DSL_postUpdateDecl___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__16_value) as *mut LeanObject;
static mut l_Lake_DSL_postUpdateDecl___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_postUpdateDecl___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_postUpdateDecl___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_postUpdateDecl___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_postUpdateDecl: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_fromPath___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [102, 114, 111, 109, 80, 97, 116, 104, 0],
};
static mut l_Lake_DSL_fromPath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_fromPath___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_fromPath___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_fromPath___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__0_value) as *mut LeanObject,
        10954861864498947928 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromPath___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_fromPath___closed__2_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lake_DSL_fromPath___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_fromPath___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__2_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromPath___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_fromPath___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__3_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromPath___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_fromPath___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromPath___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__5_value) as *mut LeanObject;
pub static mut l_Lake_DSL_fromPath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [102, 114, 111, 109, 71, 105, 116, 0],
};
static mut l_Lake_DSL_fromGit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_fromGit___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_fromGit___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_fromGit___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__0_value) as *mut LeanObject,
        8744503865935906362 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [103, 105, 116, 32, 0],
};
static mut l_Lake_DSL_fromGit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__3_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__6_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [64, 0],
};
static mut l_Lake_DSL_fromGit___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__6_value) as *mut LeanObject],
};
static mut l_Lake_DSL_fromGit___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__11_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [47, 0],
};
static mut l_Lake_DSL_fromGit___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__11_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__12_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__11_value) as *mut LeanObject],
};
static mut l_Lake_DSL_fromGit___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__12_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__13_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__14_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__14_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__15_value) as *mut LeanObject;
pub static l_Lake_DSL_fromGit___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromGit___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__16_value) as *mut LeanObject;
pub static mut l_Lake_DSL_fromGit: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__16_value) as *mut LeanObject;
pub static l_Lake_DSL_fromSource___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [102, 114, 111, 109, 83, 111, 117, 114, 99, 101, 0],
};
static mut l_Lake_DSL_fromSource___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_fromSource___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_fromSource___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_fromSource___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__0_value) as *mut LeanObject,
        10611690220945862380 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromSource___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_fromSource___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__16_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromSource___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_fromSource___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromSource___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_DSL_fromSource: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_fromClause___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [102, 114, 111, 109, 67, 108, 97, 117, 115, 101, 0],
};
static mut l_Lake_DSL_fromClause___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_fromClause___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_fromClause___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_fromClause___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__0_value) as *mut LeanObject,
        862063901515217772 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromClause___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_fromClause___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 102, 114, 111, 109, 32, 0],
};
static mut l_Lake_DSL_fromClause___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_fromClause___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_fromClause___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_fromClause___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromClause___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_fromClause___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_fromClause___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__5_value) as *mut LeanObject;
pub static mut l_Lake_DSL_fromClause: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_withClause___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [119, 105, 116, 104, 67, 108, 97, 117, 115, 101, 0],
};
static mut l_Lake_DSL_withClause___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_withClause___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_withClause___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_withClause___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_withClause___closed__0_value) as *mut LeanObject,
        15981276745742611006 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_withClause___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_withClause___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lake_DSL_withClause___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_withClause___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_withClause___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_withClause___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_withClause___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_withClause___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_withClause___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_withClause___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_withClause___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_withClause___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_withClause___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__5_value) as *mut LeanObject;
pub static mut l_Lake_DSL_withClause: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_verSpec___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [118, 101, 114, 83, 112, 101, 99, 0],
};
static mut l_Lake_DSL_verSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_verSpec___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_verSpec___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_verSpec___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__0_value) as *mut LeanObject,
        3421776117942701061 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verSpec___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_verSpec___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verSpec___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_verSpec___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verSpec___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_verSpec___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verSpec___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_DSL_verSpec: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_verClause___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [118, 101, 114, 67, 108, 97, 117, 115, 101, 0],
};
static mut l_Lake_DSL_verClause___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_verClause___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_verClause___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_verClause___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verClause___closed__0_value) as *mut LeanObject,
        16691910745100808827 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verClause___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_verClause___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 64, 32, 0],
};
static mut l_Lake_DSL_verClause___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_verClause___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_verClause___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_verClause___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_verClause___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verClause___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verClause___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_verClause___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verClause___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verClause___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verClause___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__5_value) as *mut LeanObject;
pub static mut l_Lake_DSL_verClause: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 101, 112, 78, 97, 109, 101, 0],
};
static mut l_Lake_DSL_depName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_depName___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_depName___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_depName___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__0_value) as *mut LeanObject,
        13377777968340814859 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lake_DSL_depName___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__2_value) as *mut LeanObject,
        4024150434455327032 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depName___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__4_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Lake_DSL_depName___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__4_value) as *mut LeanObject,
        9232979286016572671 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depName___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_depName___closed__5_value) as *mut LeanObject],
};
static mut l_Lake_DSL_depName___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__7_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 47, 32, 0],
};
static mut l_Lake_DSL_depName___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_depName___closed__7_value) as *mut LeanObject],
};
static mut l_Lake_DSL_depName___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depName___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depName___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_depName___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depName___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__11_value) as *mut LeanObject;
static mut l_Lake_DSL_depName___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_depName___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_depName___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_depName___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_depName: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_depSpec___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 101, 112, 83, 112, 101, 99, 0],
};
static mut l_Lake_DSL_depSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_depSpec___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_depSpec___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_depSpec___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__0_value) as *mut LeanObject,
        142218530785266487 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depSpec___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_depSpec___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verClause___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depSpec___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__2_value) as *mut LeanObject;
static mut l_Lake_DSL_depSpec___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_depSpec___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_depSpec___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depSpec___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_depSpec___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_depSpec___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_depSpec___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_withClause___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_depSpec___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__6_value) as *mut LeanObject;
static mut l_Lake_DSL_depSpec___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_depSpec___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_depSpec___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_depSpec___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_depSpec: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_requireDecl___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [114, 101, 113, 117, 105, 114, 101, 68, 101, 99, 108, 0],
};
static mut l_Lake_DSL_requireDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_requireDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_requireDecl___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_requireDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__0_value) as *mut LeanObject,
        2294773639995807415 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_requireDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_requireDecl___closed__2_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [114, 101, 113, 117, 105, 114, 101, 32, 0],
};
static mut l_Lake_DSL_requireDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_requireDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_requireDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_requireDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_requireDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_requireDecl___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_requireDecl___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_requireDecl___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_requireDecl___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_requireDecl: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeRequireDeclCommand: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_DSL_buildDeclSig___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [98, 117, 105, 108, 100, 68, 101, 99, 108, 83, 105, 103, 0],
};
static mut l_Lake_DSL_buildDeclSig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_buildDeclSig___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_buildDeclSig___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_buildDeclSig___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__0_value) as *mut LeanObject,
        14011375021470499909 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_buildDeclSig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__1_value) as *mut LeanObject;
static mut l_Lake_DSL_buildDeclSig___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_buildDeclSig___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_buildDeclSig___closed__3_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0],
};
static mut l_Lake_DSL_buildDeclSig___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__3_value) as *mut LeanObject;
static l_Lake_DSL_buildDeclSig___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lake_DSL_buildDeclSig___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lake_DSL_buildDeclSig___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__10_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_buildDeclSig___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__3_value) as *mut LeanObject,
        4498178684837002829 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_buildDeclSig___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_buildDeclSig___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 8,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value) as *mut LeanObject],
};
static mut l_Lake_DSL_buildDeclSig___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__5_value) as *mut LeanObject;
static mut l_Lake_DSL_buildDeclSig___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_buildDeclSig___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_buildDeclSig___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_buildDeclSig___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_buildDeclSig___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_buildDeclSig___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_buildDeclSig: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_moduleFacetDecl___closed__0_value: LeanStringObject<16> = LeanStringObject {
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
        109, 111, 100, 117, 108, 101, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_DSL_moduleFacetDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_moduleFacetDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__0_value) as *mut LeanObject,
        11101858149492730672 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleFacetDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleFacetDecl___closed__2_value: LeanStringObject<14> = LeanStringObject {
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
        109, 111, 100, 117, 108, 101, 95, 102, 97, 99, 101, 116, 32, 0,
    ],
};
static mut l_Lake_DSL_moduleFacetDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleFacetDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_moduleFacetDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleFacetDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleFacetDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_moduleFacetDecl___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_moduleFacetDecl___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_moduleFacetDecl___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_moduleFacetDecl___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_moduleFacetDecl: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_packageFacetDecl___closed__0_value: LeanStringObject<17> = LeanStringObject {
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
        112, 97, 99, 107, 97, 103, 101, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_DSL_packageFacetDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_packageFacetDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_packageFacetDecl___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_packageFacetDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__0_value) as *mut LeanObject,
        7094079308183198759 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageFacetDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_packageFacetDecl___closed__2_value: LeanStringObject<15> = LeanStringObject {
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
        112, 97, 99, 107, 97, 103, 101, 95, 102, 97, 99, 101, 116, 32, 0,
    ],
};
static mut l_Lake_DSL_packageFacetDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_packageFacetDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_packageFacetDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_packageFacetDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageFacetDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_packageFacetDecl___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_packageFacetDecl___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_packageFacetDecl___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_packageFacetDecl___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_packageFacetDecl: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_libraryFacetDecl___closed__0_value: LeanStringObject<17> = LeanStringObject {
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
        108, 105, 98, 114, 97, 114, 121, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_DSL_libraryFacetDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_libraryFacetDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__0_value) as *mut LeanObject,
        12396503196187142467 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_libraryFacetDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_libraryFacetDecl___closed__2_value: LeanStringObject<15> = LeanStringObject {
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
        108, 105, 98, 114, 97, 114, 121, 95, 102, 97, 99, 101, 116, 32, 0,
    ],
};
static mut l_Lake_DSL_libraryFacetDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_libraryFacetDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_libraryFacetDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_libraryFacetDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_libraryFacetDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_libraryFacetDecl___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_libraryFacetDecl___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_libraryFacetDecl___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_libraryFacetDecl___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_libraryFacetDecl: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_targetCommand___closed__0_value: LeanStringObject<14> = LeanStringObject {
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
        116, 97, 114, 103, 101, 116, 67, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lake_DSL_targetCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_targetCommand___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_targetCommand___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_targetCommand___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__0_value) as *mut LeanObject,
        13148943219030950965 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_targetCommand___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_targetCommand___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 97, 114, 103, 101, 116, 32, 0],
};
static mut l_Lake_DSL_targetCommand___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_targetCommand___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_targetCommand___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_targetCommand___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_targetCommand___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_targetCommand___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_targetCommand___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_targetCommand___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_targetCommand___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_targetCommand: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_leanLibCommand___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        108, 101, 97, 110, 76, 105, 98, 67, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lake_DSL_leanLibCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_leanLibCommand___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_leanLibCommand___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_leanLibCommand___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__0_value) as *mut LeanObject,
        11637615818822604122 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_leanLibCommand___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_leanLibCommand___closed__2_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 101, 97, 110, 95, 108, 105, 98, 32, 0],
};
static mut l_Lake_DSL_leanLibCommand___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_leanLibCommand___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_leanLibCommand___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_leanLibCommand___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_leanLibCommand___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_leanLibCommand___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_leanLibCommand___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_leanLibCommand___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_leanLibCommand___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_leanLibCommand___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_leanLibCommand___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_leanLibCommand: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeLeanLibCommandCommand: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        108, 101, 97, 110, 69, 120, 101, 67, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lake_DSL_leanExeCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_leanExeCommand___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_leanExeCommand___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_leanExeCommand___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__0_value) as *mut LeanObject,
        2062700356019151327 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_leanExeCommand___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__2_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 101, 97, 110, 95, 101, 120, 101, 32, 0],
};
static mut l_Lake_DSL_leanExeCommand___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_leanExeCommand___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_leanExeCommand___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_leanExeCommand___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_leanExeCommand___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_leanExeCommand___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_leanExeCommand___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_leanExeCommand___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_leanExeCommand___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_leanExeCommand: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeLeanExeCommandCommand: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__0_value: LeanStringObject<17> = LeanStringObject {
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
        105, 110, 112, 117, 116, 70, 105, 108, 101, 67, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lake_DSL_inputFileCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_inputFileCommand___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_inputFileCommand___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_inputFileCommand___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__0_value) as *mut LeanObject,
        10121707264994059151 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_inputFileCommand___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__2_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [105, 110, 112, 117, 116, 95, 102, 105, 108, 101, 32, 0],
};
static mut l_Lake_DSL_inputFileCommand___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_inputFileCommand___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_inputFileCommand___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_inputFileCommand___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_inputFileCommand___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_inputFileCommand___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_inputFileCommand___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_inputFileCommand___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_inputFileCommand___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_inputFileCommand: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeInputFileCommandCommand: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__0_value: LeanStringObject<16> = LeanStringObject {
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
        105, 110, 112, 117, 116, 68, 105, 114, 67, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lake_DSL_inputDirCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_inputDirCommand___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_inputDirCommand___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_inputDirCommand___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__0_value) as *mut LeanObject,
        8119030422813828009 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_inputDirCommand___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__2_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 112, 117, 116, 95, 100, 105, 114, 32, 0],
};
static mut l_Lake_DSL_inputDirCommand___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_inputDirCommand___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_inputDirCommand___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_inputDirCommand___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_inputDirCommand___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_inputDirCommand___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_inputDirCommand___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_inputDirCommand___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_inputDirCommand___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_inputDirCommand: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeInputDirCommandCommand: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_DSL_externLibDeclSpec___closed__0_value: LeanStringObject<18> =
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
            101, 120, 116, 101, 114, 110, 76, 105, 98, 68, 101, 99, 108, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lake_DSL_externLibDeclSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_externLibDeclSpec___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__0_value) as *mut LeanObject,
        12740147664822022041 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_externLibDeclSpec___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__1_value) as *mut LeanObject;
static mut l_Lake_DSL_externLibDeclSpec___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_externLibDeclSpec___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_externLibDeclSpec___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_externLibDeclSpec___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_externLibDeclSpec: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_externLibCommand___closed__0_value: LeanStringObject<17> = LeanStringObject {
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
        101, 120, 116, 101, 114, 110, 76, 105, 98, 67, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lake_DSL_externLibCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_externLibCommand___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_externLibCommand___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_externLibCommand___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__0_value) as *mut LeanObject,
        9360286785500177995 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_externLibCommand___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_externLibCommand___closed__2_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [101, 120, 116, 101, 114, 110, 95, 108, 105, 98, 32, 0],
};
static mut l_Lake_DSL_externLibCommand___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_externLibCommand___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_externLibCommand___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_externLibCommand___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_externLibCommand___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_externLibCommand___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_externLibCommand___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_externLibCommand___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_externLibCommand___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_externLibCommand: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_scriptDeclSpec___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        115, 99, 114, 105, 112, 116, 68, 101, 99, 108, 83, 112, 101, 99, 0,
    ],
};
static mut l_Lake_DSL_scriptDeclSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_scriptDeclSpec___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__0_value) as *mut LeanObject,
        7959617833543045482 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_scriptDeclSpec___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__1_value) as *mut LeanObject;
static mut l_Lake_DSL_scriptDeclSpec___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_scriptDeclSpec___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_scriptDeclSpec___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_scriptDeclSpec___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_scriptDeclSpec: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_scriptDecl___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 99, 114, 105, 112, 116, 68, 101, 99, 108, 0],
};
static mut l_Lake_DSL_scriptDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_scriptDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_scriptDecl___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_scriptDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__0_value) as *mut LeanObject,
        11447824861308129923 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_scriptDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_scriptDecl___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 99, 114, 105, 112, 116, 32, 0],
};
static mut l_Lake_DSL_scriptDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_scriptDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_scriptDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_scriptDecl___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_scriptDecl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__4_value) as *mut LeanObject;
static mut l_Lake_DSL_scriptDecl___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_scriptDecl___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_scriptDecl___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_DSL_scriptDecl___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_scriptDecl: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_verLit___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [118, 101, 114, 76, 105, 116, 0],
};
static mut l_Lake_DSL_verLit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_verLit___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_verLit___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_verLit___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__0_value) as *mut LeanObject,
        9704141730406518167 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verLit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [118, 33, 0],
};
static mut l_Lake_DSL_verLit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_verLit___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_verLit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__4_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lake_DSL_verLit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__4_value) as *mut LeanObject,
        1581446985683836252 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verLit___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_verLit___closed__5_value) as *mut LeanObject],
};
static mut l_Lake_DSL_verLit___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verLit___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__8_value: LeanStringObject<16> = LeanStringObject {
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
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
    ],
};
static mut l_Lake_DSL_verLit___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__8_value) as *mut LeanObject,
        18163029821153688220 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verLit___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verLit___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verLit___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__11_value) as *mut LeanObject;
pub static l_Lake_DSL_verLit___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_verLit___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__12_value) as *mut LeanObject;
pub static mut l_Lake_DSL_verLit: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__12_value) as *mut LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [102, 97, 99, 101, 116, 83, 117, 102, 102, 105, 120, 0],
};
static mut l_Lake_DSL_facetSuffix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_facetSuffix___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_facetSuffix___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_facetSuffix___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__0_value) as *mut LeanObject,
        7856869693164098343 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_facetSuffix___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l_Lake_DSL_facetSuffix___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_facetSuffix___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_facetSuffix___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_facetSuffix___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_facetSuffix___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_facetSuffix___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value) as *mut LeanObject;
pub static mut l_Lake_DSL_facetSuffix: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__0_value: LeanStringObject<17> = LeanStringObject {
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
        112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 76, 105, 116, 0,
    ],
};
static mut l_Lake_DSL_packageTargetLit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_packageTargetLit___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_packageTargetLit___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_packageTargetLit___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__0_value) as *mut LeanObject,
        6142289428472292793 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetLit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__2_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lake_DSL_packageTargetLit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_packageTargetLit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetLit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetLit___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetLit___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetLit___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetLit___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__8_value) as *mut LeanObject;
pub static mut l_Lake_DSL_packageTargetLit: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__0_value: LeanStringObject<19> =
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
            109, 111, 100, 117, 108, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116, 0,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_moduleTargetKeyLit___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__0_value) as *mut LeanObject,
        4666197752279438947 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleTargetKeyLit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__2_value: LeanStringObject<3> =
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
        m_data: [96, 43, 0],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleTargetKeyLit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleTargetKeyLit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleTargetKeyLit___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__6_value: LeanStringObject<5> =
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
static mut l_Lake_DSL_moduleTargetKeyLit___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__6_value) as *mut LeanObject,
        2302572775315350313 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleTargetKeyLit___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleTargetKeyLit___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleTargetKeyLit___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_moduleTargetKeyLit___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__10_value) as *mut LeanObject;
pub static mut l_Lake_DSL_moduleTargetKeyLit: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__0_value: LeanStringObject<20> =
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
            112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116,
            0,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_packageTargetKeyLit___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__0_value) as *mut LeanObject,
        17001465581052579529 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__2_value: LeanStringObject<3> =
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
        m_data: [96, 64, 0],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__11_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__12_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__13_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__14_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__14_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__15_value) as *mut LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_packageTargetKeyLit___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__16_value) as *mut LeanObject;
pub static mut l_Lake_DSL_packageTargetKeyLit: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__16_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 109, 100, 68, 111, 0],
};
static mut l_Lake_DSL_cmdDo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_cmdDo___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_cmdDo___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_cmdDo___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__0_value) as *mut LeanObject,
        4812447225742894945 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__2_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lake_DSL_cmdDo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__2_value) as *mut LeanObject,
        2214559063752339918 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__4_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [100, 111, 0],
};
static mut l_Lake_DSL_cmdDo___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__4_value) as *mut LeanObject],
};
static mut l_Lake_DSL_cmdDo___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__6_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [109, 97, 110, 121, 49, 73, 110, 100, 101, 110, 116, 0],
};
static mut l_Lake_DSL_cmdDo___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__6_value) as *mut LeanObject,
        16727513630015613089 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__8_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lake_DSL_cmdDo___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__8_value) as *mut LeanObject,
        5063646790596052253 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__9_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__11_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__12_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__13_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__13_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__14_value) as *mut LeanObject;
pub static l_Lake_DSL_cmdDo___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_cmdDo___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value) as *mut LeanObject;
pub static mut l_Lake_DSL_cmdDo: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 101, 116, 97, 73, 102, 0],
};
static mut l_Lake_DSL_metaIf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_metaIf___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_metaIf___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_metaIf___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__0_value) as *mut LeanObject,
        14561490878273970730 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_metaIf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [109, 101, 116, 97, 32, 0],
};
static mut l_Lake_DSL_metaIf___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_metaIf___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__4_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 102, 32, 0],
};
static mut l_Lake_DSL_metaIf___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__4_value) as *mut LeanObject],
};
static mut l_Lake_DSL_metaIf___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_metaIf___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_metaIf___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__8_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 116, 104, 101, 110, 32, 0],
};
static mut l_Lake_DSL_metaIf___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__8_value) as *mut LeanObject],
};
static mut l_Lake_DSL_metaIf___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_metaIf___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_metaIf___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__11_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__12_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 101, 108, 115, 101, 32, 0],
};
static mut l_Lake_DSL_metaIf___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__12_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__13_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__12_value) as *mut LeanObject],
};
static mut l_Lake_DSL_metaIf___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__13_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__13_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_metaIf___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__14_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__15_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_metaIf___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__15_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_metaIf___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__16_value) as *mut LeanObject;
pub static l_Lake_DSL_metaIf___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_metaIf___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__17_value) as *mut LeanObject;
pub static mut l_Lake_DSL_metaIf: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__17_value) as *mut LeanObject;
pub static l_Lake_DSL_runIO___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 117, 110, 73, 79, 0],
};
static mut l_Lake_DSL_runIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__0_value) as *mut LeanObject;
static l_Lake_DSL_runIO___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_DSL_runIO___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut LeanObject,
        5901868804703194544 as *mut LeanObject,
    ],
};
pub static l_Lake_DSL_runIO___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_runIO___closed__0_value) as *mut LeanObject,
        891786894088060352 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_runIO___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_runIO___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 117, 110, 95, 105, 111, 32, 0],
};
static mut l_Lake_DSL_runIO___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_runIO___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_runIO___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_DSL_runIO___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__3_value) as *mut LeanObject;
pub static l_Lake_DSL_runIO___closed__4_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [100, 111, 83, 101, 113, 0],
};
static mut l_Lake_DSL_runIO___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__4_value) as *mut LeanObject;
pub static l_Lake_DSL_runIO___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_runIO___closed__4_value) as *mut LeanObject,
        12922580977142754391 as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_runIO___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_runIO___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_DSL_runIO___closed__5_value) as *mut LeanObject],
};
static mut l_Lake_DSL_runIO___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_runIO___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_runIO___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_runIO___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_runIO___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_runIO___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_runIO___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_DSL_runIO___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__8_value) as *mut LeanObject;
pub static mut l_Lake_DSL_runIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__8_value) as *mut LeanObject;
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__19() -> *mut LeanObject {
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_Lake_DSL_identOrStr;
    v___x_1068_ = l_Lake_DSL_packageCommand___closed__3;
    v___x_1069_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1069_, 0, v___x_1068_);
    lean_ctor_set(v___x_1069_, 1, v___x_1067_);
    return v___x_1069_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__20() -> *mut LeanObject {
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    v___x_1070_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1071_ = l_Lake_DSL_packageCommand___closed__18;
    v___x_1072_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1073_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1073_, 0, v___x_1072_);
    lean_ctor_set(v___x_1073_, 1, v___x_1071_);
    lean_ctor_set(v___x_1073_, 2, v___x_1070_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__21() -> *mut LeanObject {
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    v___x_1074_ = l_Lake_DSL_optConfig;
    v___x_1075_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__20),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__20_once),
        _init_l_Lake_DSL_packageCommand___closed__20,
    );
    v___x_1076_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1077_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1077_, 0, v___x_1076_);
    lean_ctor_set(v___x_1077_, 1, v___x_1075_);
    lean_ctor_set(v___x_1077_, 2, v___x_1074_);
    return v___x_1077_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__22() -> *mut LeanObject {
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    v___x_1078_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__21),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__21_once),
        _init_l_Lake_DSL_packageCommand___closed__21,
    );
    v___x_1079_ = lean_unsigned_to_nat(1022);
    v___x_1080_ = l_Lake_DSL_packageCommand___closed__1;
    v___x_1081_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1081_, 0, v___x_1080_);
    lean_ctor_set(v___x_1081_, 1, v___x_1079_);
    lean_ctor_set(v___x_1081_, 2, v___x_1078_);
    return v___x_1081_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand() -> *mut LeanObject {
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    v___x_1082_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__22),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__22_once),
        _init_l_Lake_DSL_packageCommand___closed__22,
    );
    return v___x_1082_;
}
pub unsafe fn l_Lake_DSL_instCoePackageCommandCommand___lam__0(
    mut v_x_1083_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1083_);
    return v_x_1083_;
}
pub unsafe fn l_Lake_DSL_instCoePackageCommandCommand___lam__0___boxed(
    mut v_x_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1085_: *mut LeanObject = core::ptr::null_mut();
    v_res_1085_ = l_Lake_DSL_instCoePackageCommandCommand___lam__0(v_x_1084_);
    lean_dec(v_x_1084_);
    return v_res_1085_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__8() -> *mut LeanObject {
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_Lake_DSL_simpleBinder;
    v___x_1106_ = l_Lake_DSL_postUpdateDecl___closed__7;
    v___x_1107_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1108_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1108_, 0, v___x_1107_);
    lean_ctor_set(v___x_1108_, 1, v___x_1106_);
    lean_ctor_set(v___x_1108_, 2, v___x_1105_);
    return v___x_1108_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__9() -> *mut LeanObject {
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    v___x_1109_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__8),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__8_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__8,
    );
    v___x_1110_ = l_Lake_DSL_packageCommand___closed__3;
    v___x_1111_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1111_, 0, v___x_1110_);
    lean_ctor_set(v___x_1111_, 1, v___x_1109_);
    return v___x_1111_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__10() -> *mut LeanObject {
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    v___x_1112_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__9,
    );
    v___x_1113_ = l_Lake_DSL_postUpdateDecl___closed__4;
    v___x_1114_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1115_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1115_, 0, v___x_1114_);
    lean_ctor_set(v___x_1115_, 1, v___x_1113_);
    lean_ctor_set(v___x_1115_, 2, v___x_1112_);
    return v___x_1115_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__17() -> *mut LeanObject {
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    v___x_1128_ = l_Lake_DSL_declValDo;
    v___x_1129_ = l_Lake_DSL_postUpdateDecl___closed__16;
    v___x_1130_ = l_Lake_DSL_postUpdateDecl___closed__12;
    v___x_1131_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1131_, 0, v___x_1130_);
    lean_ctor_set(v___x_1131_, 1, v___x_1129_);
    lean_ctor_set(v___x_1131_, 2, v___x_1128_);
    return v___x_1131_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__18() -> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__17,
    );
    v___x_1133_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__10),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__10_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__10,
    );
    v___x_1134_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1135_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1135_, 0, v___x_1134_);
    lean_ctor_set(v___x_1135_, 1, v___x_1133_);
    lean_ctor_set(v___x_1135_, 2, v___x_1132_);
    return v___x_1135_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__19() -> *mut LeanObject {
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    v___x_1136_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__18),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__18_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__18,
    );
    v___x_1137_ = lean_unsigned_to_nat(1022);
    v___x_1138_ = l_Lake_DSL_postUpdateDecl___closed__1;
    v___x_1139_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1139_, 0, v___x_1138_);
    lean_ctor_set(v___x_1139_, 1, v___x_1137_);
    lean_ctor_set(v___x_1139_, 2, v___x_1136_);
    return v___x_1139_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl() -> *mut LeanObject {
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    v___x_1140_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__19_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__19,
    );
    return v___x_1140_;
}
pub unsafe fn _init_l_Lake_DSL_depName___closed__12() -> *mut LeanObject {
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_Lake_DSL_identOrStr;
    v___x_1315_ = l_Lake_DSL_depName___closed__11;
    v___x_1316_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1317_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1317_, 0, v___x_1316_);
    lean_ctor_set(v___x_1317_, 1, v___x_1315_);
    lean_ctor_set(v___x_1317_, 2, v___x_1314_);
    return v___x_1317_;
}
pub unsafe fn _init_l_Lake_DSL_depName___closed__13() -> *mut LeanObject {
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    v___x_1318_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__12),
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__12_once),
        _init_l_Lake_DSL_depName___closed__12,
    );
    v___x_1319_ = l_Lake_DSL_depName___closed__1;
    v___x_1320_ = l_Lake_DSL_depName___closed__0;
    v___x_1321_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_1321_, 0, v___x_1320_);
    lean_ctor_set(v___x_1321_, 1, v___x_1319_);
    lean_ctor_set(v___x_1321_, 2, v___x_1318_);
    return v___x_1321_;
}
pub unsafe fn _init_l_Lake_DSL_depName() -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    v___x_1322_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__13),
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__13_once),
        _init_l_Lake_DSL_depName___closed__13,
    );
    return v___x_1322_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__3() -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    v___x_1331_ = l_Lake_DSL_depSpec___closed__2;
    v___x_1332_ = l_Lake_DSL_depName;
    v___x_1333_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1334_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1334_, 0, v___x_1333_);
    lean_ctor_set(v___x_1334_, 1, v___x_1332_);
    lean_ctor_set(v___x_1334_, 2, v___x_1331_);
    return v___x_1334_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__5() -> *mut LeanObject {
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    v___x_1338_ = l_Lake_DSL_depSpec___closed__4;
    v___x_1339_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__3_once),
        _init_l_Lake_DSL_depSpec___closed__3,
    );
    v___x_1340_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1341_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1341_, 0, v___x_1340_);
    lean_ctor_set(v___x_1341_, 1, v___x_1339_);
    lean_ctor_set(v___x_1341_, 2, v___x_1338_);
    return v___x_1341_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__7() -> *mut LeanObject {
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    v___x_1345_ = l_Lake_DSL_depSpec___closed__6;
    v___x_1346_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__5_once),
        _init_l_Lake_DSL_depSpec___closed__5,
    );
    v___x_1347_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1348_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1348_, 0, v___x_1347_);
    lean_ctor_set(v___x_1348_, 1, v___x_1346_);
    lean_ctor_set(v___x_1348_, 2, v___x_1345_);
    return v___x_1348_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__8() -> *mut LeanObject {
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    v___x_1349_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__7_once),
        _init_l_Lake_DSL_depSpec___closed__7,
    );
    v___x_1350_ = l_Lake_DSL_depSpec___closed__1;
    v___x_1351_ = l_Lake_DSL_depSpec___closed__0;
    v___x_1352_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_1352_, 0, v___x_1351_);
    lean_ctor_set(v___x_1352_, 1, v___x_1350_);
    lean_ctor_set(v___x_1352_, 2, v___x_1349_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec() -> *mut LeanObject {
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    v___x_1353_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__8),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__8_once),
        _init_l_Lake_DSL_depSpec___closed__8,
    );
    return v___x_1353_;
}
pub unsafe fn _init_l_Lake_DSL_requireDecl___closed__5() -> *mut LeanObject {
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lake_DSL_depSpec;
    v___x_1367_ = l_Lake_DSL_requireDecl___closed__4;
    v___x_1368_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1369_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1369_, 0, v___x_1368_);
    lean_ctor_set(v___x_1369_, 1, v___x_1367_);
    lean_ctor_set(v___x_1369_, 2, v___x_1366_);
    return v___x_1369_;
}
pub unsafe fn _init_l_Lake_DSL_requireDecl___closed__6() -> *mut LeanObject {
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    v___x_1370_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__5_once),
        _init_l_Lake_DSL_requireDecl___closed__5,
    );
    v___x_1371_ = lean_unsigned_to_nat(1022);
    v___x_1372_ = l_Lake_DSL_requireDecl___closed__1;
    v___x_1373_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1373_, 0, v___x_1372_);
    lean_ctor_set(v___x_1373_, 1, v___x_1371_);
    lean_ctor_set(v___x_1373_, 2, v___x_1370_);
    return v___x_1373_;
}
pub unsafe fn _init_l_Lake_DSL_requireDecl() -> *mut LeanObject {
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    v___x_1374_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__6_once),
        _init_l_Lake_DSL_requireDecl___closed__6,
    );
    return v___x_1374_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__2() -> *mut LeanObject {
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    v___x_1381_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__9,
    );
    v___x_1382_ = l_Lake_DSL_identOrStr;
    v___x_1383_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1384_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1384_, 0, v___x_1383_);
    lean_ctor_set(v___x_1384_, 1, v___x_1382_);
    lean_ctor_set(v___x_1384_, 2, v___x_1381_);
    return v___x_1384_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__6() -> *mut LeanObject {
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Lake_DSL_buildDeclSig___closed__5;
    v___x_1394_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2_once),
        _init_l_Lake_DSL_buildDeclSig___closed__2,
    );
    v___x_1395_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1396_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1396_, 0, v___x_1395_);
    lean_ctor_set(v___x_1396_, 1, v___x_1394_);
    lean_ctor_set(v___x_1396_, 2, v___x_1393_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__7() -> *mut LeanObject {
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    v___x_1397_ = l_Lake_DSL_postUpdateDecl___closed__16;
    v___x_1398_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__6_once),
        _init_l_Lake_DSL_buildDeclSig___closed__6,
    );
    v___x_1399_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1400_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1400_, 0, v___x_1399_);
    lean_ctor_set(v___x_1400_, 1, v___x_1398_);
    lean_ctor_set(v___x_1400_, 2, v___x_1397_);
    return v___x_1400_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__8() -> *mut LeanObject {
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1401_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__7_once),
        _init_l_Lake_DSL_buildDeclSig___closed__7,
    );
    v___x_1402_ = l_Lake_DSL_buildDeclSig___closed__1;
    v___x_1403_ = l_Lake_DSL_buildDeclSig___closed__0;
    v___x_1404_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    lean_ctor_set(v___x_1404_, 1, v___x_1402_);
    lean_ctor_set(v___x_1404_, 2, v___x_1401_);
    return v___x_1404_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig() -> *mut LeanObject {
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    v___x_1405_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__8),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__8_once),
        _init_l_Lake_DSL_buildDeclSig___closed__8,
    );
    return v___x_1405_;
}
pub unsafe fn _init_l_Lake_DSL_moduleFacetDecl___closed__5() -> *mut LeanObject {
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    v___x_1418_ = l_Lake_DSL_buildDeclSig;
    v___x_1419_ = l_Lake_DSL_moduleFacetDecl___closed__4;
    v___x_1420_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1421_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1421_, 0, v___x_1420_);
    lean_ctor_set(v___x_1421_, 1, v___x_1419_);
    lean_ctor_set(v___x_1421_, 2, v___x_1418_);
    return v___x_1421_;
}
pub unsafe fn _init_l_Lake_DSL_moduleFacetDecl___closed__6() -> *mut LeanObject {
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    v___x_1422_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__5_once),
        _init_l_Lake_DSL_moduleFacetDecl___closed__5,
    );
    v___x_1423_ = lean_unsigned_to_nat(1022);
    v___x_1424_ = l_Lake_DSL_moduleFacetDecl___closed__1;
    v___x_1425_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1425_, 0, v___x_1424_);
    lean_ctor_set(v___x_1425_, 1, v___x_1423_);
    lean_ctor_set(v___x_1425_, 2, v___x_1422_);
    return v___x_1425_;
}
pub unsafe fn _init_l_Lake_DSL_moduleFacetDecl() -> *mut LeanObject {
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1426_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__6_once),
        _init_l_Lake_DSL_moduleFacetDecl___closed__6,
    );
    return v___x_1426_;
}
pub unsafe fn _init_l_Lake_DSL_packageFacetDecl___closed__5() -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Lake_DSL_buildDeclSig;
    v___x_1440_ = l_Lake_DSL_packageFacetDecl___closed__4;
    v___x_1441_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1442_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1442_, 0, v___x_1441_);
    lean_ctor_set(v___x_1442_, 1, v___x_1440_);
    lean_ctor_set(v___x_1442_, 2, v___x_1439_);
    return v___x_1442_;
}
pub unsafe fn _init_l_Lake_DSL_packageFacetDecl___closed__6() -> *mut LeanObject {
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    v___x_1443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__5_once),
        _init_l_Lake_DSL_packageFacetDecl___closed__5,
    );
    v___x_1444_ = lean_unsigned_to_nat(1022);
    v___x_1445_ = l_Lake_DSL_packageFacetDecl___closed__1;
    v___x_1446_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1446_, 0, v___x_1445_);
    lean_ctor_set(v___x_1446_, 1, v___x_1444_);
    lean_ctor_set(v___x_1446_, 2, v___x_1443_);
    return v___x_1446_;
}
pub unsafe fn _init_l_Lake_DSL_packageFacetDecl() -> *mut LeanObject {
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    v___x_1447_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__6_once),
        _init_l_Lake_DSL_packageFacetDecl___closed__6,
    );
    return v___x_1447_;
}
pub unsafe fn _init_l_Lake_DSL_libraryFacetDecl___closed__5() -> *mut LeanObject {
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1460_ = l_Lake_DSL_buildDeclSig;
    v___x_1461_ = l_Lake_DSL_libraryFacetDecl___closed__4;
    v___x_1462_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1463_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1463_, 0, v___x_1462_);
    lean_ctor_set(v___x_1463_, 1, v___x_1461_);
    lean_ctor_set(v___x_1463_, 2, v___x_1460_);
    return v___x_1463_;
}
pub unsafe fn _init_l_Lake_DSL_libraryFacetDecl___closed__6() -> *mut LeanObject {
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    v___x_1464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__5_once),
        _init_l_Lake_DSL_libraryFacetDecl___closed__5,
    );
    v___x_1465_ = lean_unsigned_to_nat(1022);
    v___x_1466_ = l_Lake_DSL_libraryFacetDecl___closed__1;
    v___x_1467_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1467_, 0, v___x_1466_);
    lean_ctor_set(v___x_1467_, 1, v___x_1465_);
    lean_ctor_set(v___x_1467_, 2, v___x_1464_);
    return v___x_1467_;
}
pub unsafe fn _init_l_Lake_DSL_libraryFacetDecl() -> *mut LeanObject {
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    v___x_1468_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__6_once),
        _init_l_Lake_DSL_libraryFacetDecl___closed__6,
    );
    return v___x_1468_;
}
pub unsafe fn _init_l_Lake_DSL_targetCommand___closed__5() -> *mut LeanObject {
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    v___x_1481_ = l_Lake_DSL_buildDeclSig;
    v___x_1482_ = l_Lake_DSL_targetCommand___closed__4;
    v___x_1483_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1484_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1484_, 0, v___x_1483_);
    lean_ctor_set(v___x_1484_, 1, v___x_1482_);
    lean_ctor_set(v___x_1484_, 2, v___x_1481_);
    return v___x_1484_;
}
pub unsafe fn _init_l_Lake_DSL_targetCommand___closed__6() -> *mut LeanObject {
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    v___x_1485_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__5_once),
        _init_l_Lake_DSL_targetCommand___closed__5,
    );
    v___x_1486_ = lean_unsigned_to_nat(1022);
    v___x_1487_ = l_Lake_DSL_targetCommand___closed__1;
    v___x_1488_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1488_, 0, v___x_1487_);
    lean_ctor_set(v___x_1488_, 1, v___x_1486_);
    lean_ctor_set(v___x_1488_, 2, v___x_1485_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lake_DSL_targetCommand() -> *mut LeanObject {
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    v___x_1489_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__6_once),
        _init_l_Lake_DSL_targetCommand___closed__6,
    );
    return v___x_1489_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand___closed__5() -> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1503_ = l_Lake_DSL_leanLibCommand___closed__4;
    v___x_1504_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1505_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1505_, 0, v___x_1504_);
    lean_ctor_set(v___x_1505_, 1, v___x_1503_);
    lean_ctor_set(v___x_1505_, 2, v___x_1502_);
    return v___x_1505_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand___closed__6() -> *mut LeanObject {
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    v___x_1506_ = l_Lake_DSL_optConfig;
    v___x_1507_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__5_once),
        _init_l_Lake_DSL_leanLibCommand___closed__5,
    );
    v___x_1508_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1509_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1509_, 0, v___x_1508_);
    lean_ctor_set(v___x_1509_, 1, v___x_1507_);
    lean_ctor_set(v___x_1509_, 2, v___x_1506_);
    return v___x_1509_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand___closed__7() -> *mut LeanObject {
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v___x_1510_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__6_once),
        _init_l_Lake_DSL_leanLibCommand___closed__6,
    );
    v___x_1511_ = lean_unsigned_to_nat(1022);
    v___x_1512_ = l_Lake_DSL_leanLibCommand___closed__1;
    v___x_1513_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    lean_ctor_set(v___x_1513_, 1, v___x_1511_);
    lean_ctor_set(v___x_1513_, 2, v___x_1510_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand() -> *mut LeanObject {
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    v___x_1514_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__7_once),
        _init_l_Lake_DSL_leanLibCommand___closed__7,
    );
    return v___x_1514_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand___closed__5() -> *mut LeanObject {
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1529_ = l_Lake_DSL_leanExeCommand___closed__4;
    v___x_1530_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1531_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    lean_ctor_set(v___x_1531_, 1, v___x_1529_);
    lean_ctor_set(v___x_1531_, 2, v___x_1528_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand___closed__6() -> *mut LeanObject {
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    v___x_1532_ = l_Lake_DSL_optConfig;
    v___x_1533_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__5_once),
        _init_l_Lake_DSL_leanExeCommand___closed__5,
    );
    v___x_1534_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1535_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1535_, 0, v___x_1534_);
    lean_ctor_set(v___x_1535_, 1, v___x_1533_);
    lean_ctor_set(v___x_1535_, 2, v___x_1532_);
    return v___x_1535_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand___closed__7() -> *mut LeanObject {
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    v___x_1536_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__6_once),
        _init_l_Lake_DSL_leanExeCommand___closed__6,
    );
    v___x_1537_ = lean_unsigned_to_nat(1022);
    v___x_1538_ = l_Lake_DSL_leanExeCommand___closed__1;
    v___x_1539_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1539_, 0, v___x_1538_);
    lean_ctor_set(v___x_1539_, 1, v___x_1537_);
    lean_ctor_set(v___x_1539_, 2, v___x_1536_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand() -> *mut LeanObject {
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    v___x_1540_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__7_once),
        _init_l_Lake_DSL_leanExeCommand___closed__7,
    );
    return v___x_1540_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand___closed__5() -> *mut LeanObject {
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    v___x_1554_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1555_ = l_Lake_DSL_inputFileCommand___closed__4;
    v___x_1556_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1557_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1557_, 0, v___x_1556_);
    lean_ctor_set(v___x_1557_, 1, v___x_1555_);
    lean_ctor_set(v___x_1557_, 2, v___x_1554_);
    return v___x_1557_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand___closed__6() -> *mut LeanObject {
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    v___x_1558_ = l_Lake_DSL_optConfig;
    v___x_1559_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__5_once),
        _init_l_Lake_DSL_inputFileCommand___closed__5,
    );
    v___x_1560_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1561_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1561_, 0, v___x_1560_);
    lean_ctor_set(v___x_1561_, 1, v___x_1559_);
    lean_ctor_set(v___x_1561_, 2, v___x_1558_);
    return v___x_1561_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand___closed__7() -> *mut LeanObject {
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    v___x_1562_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__6_once),
        _init_l_Lake_DSL_inputFileCommand___closed__6,
    );
    v___x_1563_ = lean_unsigned_to_nat(1022);
    v___x_1564_ = l_Lake_DSL_inputFileCommand___closed__1;
    v___x_1565_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1565_, 0, v___x_1564_);
    lean_ctor_set(v___x_1565_, 1, v___x_1563_);
    lean_ctor_set(v___x_1565_, 2, v___x_1562_);
    return v___x_1565_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand() -> *mut LeanObject {
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    v___x_1566_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__7_once),
        _init_l_Lake_DSL_inputFileCommand___closed__7,
    );
    return v___x_1566_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand___closed__5() -> *mut LeanObject {
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    v___x_1580_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1581_ = l_Lake_DSL_inputDirCommand___closed__4;
    v___x_1582_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1583_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1583_, 0, v___x_1582_);
    lean_ctor_set(v___x_1583_, 1, v___x_1581_);
    lean_ctor_set(v___x_1583_, 2, v___x_1580_);
    return v___x_1583_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand___closed__6() -> *mut LeanObject {
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lake_DSL_optConfig;
    v___x_1585_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__5_once),
        _init_l_Lake_DSL_inputDirCommand___closed__5,
    );
    v___x_1586_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1587_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1587_, 0, v___x_1586_);
    lean_ctor_set(v___x_1587_, 1, v___x_1585_);
    lean_ctor_set(v___x_1587_, 2, v___x_1584_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand___closed__7() -> *mut LeanObject {
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    v___x_1588_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__6_once),
        _init_l_Lake_DSL_inputDirCommand___closed__6,
    );
    v___x_1589_ = lean_unsigned_to_nat(1022);
    v___x_1590_ = l_Lake_DSL_inputDirCommand___closed__1;
    v___x_1591_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1591_, 0, v___x_1590_);
    lean_ctor_set(v___x_1591_, 1, v___x_1589_);
    lean_ctor_set(v___x_1591_, 2, v___x_1588_);
    return v___x_1591_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand() -> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    v___x_1592_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__7_once),
        _init_l_Lake_DSL_inputDirCommand___closed__7,
    );
    return v___x_1592_;
}
pub unsafe fn _init_l_Lake_DSL_externLibDeclSpec___closed__2() -> *mut LeanObject {
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lake_DSL_postUpdateDecl___closed__16;
    v___x_1600_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2_once),
        _init_l_Lake_DSL_buildDeclSig___closed__2,
    );
    v___x_1601_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1602_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1602_, 0, v___x_1601_);
    lean_ctor_set(v___x_1602_, 1, v___x_1600_);
    lean_ctor_set(v___x_1602_, 2, v___x_1599_);
    return v___x_1602_;
}
pub unsafe fn _init_l_Lake_DSL_externLibDeclSpec___closed__3() -> *mut LeanObject {
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    v___x_1603_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__2_once),
        _init_l_Lake_DSL_externLibDeclSpec___closed__2,
    );
    v___x_1604_ = l_Lake_DSL_externLibDeclSpec___closed__1;
    v___x_1605_ = l_Lake_DSL_externLibDeclSpec___closed__0;
    v___x_1606_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_1606_, 0, v___x_1605_);
    lean_ctor_set(v___x_1606_, 1, v___x_1604_);
    lean_ctor_set(v___x_1606_, 2, v___x_1603_);
    return v___x_1606_;
}
pub unsafe fn _init_l_Lake_DSL_externLibDeclSpec() -> *mut LeanObject {
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    v___x_1607_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__3_once),
        _init_l_Lake_DSL_externLibDeclSpec___closed__3,
    );
    return v___x_1607_;
}
pub unsafe fn _init_l_Lake_DSL_externLibCommand___closed__5() -> *mut LeanObject {
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Lake_DSL_externLibDeclSpec;
    v___x_1621_ = l_Lake_DSL_externLibCommand___closed__4;
    v___x_1622_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1623_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1623_, 0, v___x_1622_);
    lean_ctor_set(v___x_1623_, 1, v___x_1621_);
    lean_ctor_set(v___x_1623_, 2, v___x_1620_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Lake_DSL_externLibCommand___closed__6() -> *mut LeanObject {
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    v___x_1624_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__5_once),
        _init_l_Lake_DSL_externLibCommand___closed__5,
    );
    v___x_1625_ = lean_unsigned_to_nat(1022);
    v___x_1626_ = l_Lake_DSL_externLibCommand___closed__1;
    v___x_1627_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1627_, 0, v___x_1626_);
    lean_ctor_set(v___x_1627_, 1, v___x_1625_);
    lean_ctor_set(v___x_1627_, 2, v___x_1624_);
    return v___x_1627_;
}
pub unsafe fn _init_l_Lake_DSL_externLibCommand() -> *mut LeanObject {
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    v___x_1628_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__6_once),
        _init_l_Lake_DSL_externLibCommand___closed__6,
    );
    return v___x_1628_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDeclSpec___closed__2() -> *mut LeanObject {
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    v___x_1634_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__17,
    );
    v___x_1635_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2_once),
        _init_l_Lake_DSL_buildDeclSig___closed__2,
    );
    v___x_1636_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1637_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1637_, 0, v___x_1636_);
    lean_ctor_set(v___x_1637_, 1, v___x_1635_);
    lean_ctor_set(v___x_1637_, 2, v___x_1634_);
    return v___x_1637_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDeclSpec___closed__3() -> *mut LeanObject {
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    v___x_1638_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__2_once),
        _init_l_Lake_DSL_scriptDeclSpec___closed__2,
    );
    v___x_1639_ = l_Lake_DSL_scriptDeclSpec___closed__1;
    v___x_1640_ = l_Lake_DSL_scriptDeclSpec___closed__0;
    v___x_1641_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_1641_, 0, v___x_1640_);
    lean_ctor_set(v___x_1641_, 1, v___x_1639_);
    lean_ctor_set(v___x_1641_, 2, v___x_1638_);
    return v___x_1641_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDeclSpec() -> *mut LeanObject {
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    v___x_1642_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__3_once),
        _init_l_Lake_DSL_scriptDeclSpec___closed__3,
    );
    return v___x_1642_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDecl___closed__5() -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Lake_DSL_scriptDeclSpec;
    v___x_1656_ = l_Lake_DSL_scriptDecl___closed__4;
    v___x_1657_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1658_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1658_, 0, v___x_1657_);
    lean_ctor_set(v___x_1658_, 1, v___x_1656_);
    lean_ctor_set(v___x_1658_, 2, v___x_1655_);
    return v___x_1658_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDecl___closed__6() -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__5_once),
        _init_l_Lake_DSL_scriptDecl___closed__5,
    );
    v___x_1660_ = lean_unsigned_to_nat(1022);
    v___x_1661_ = l_Lake_DSL_scriptDecl___closed__1;
    v___x_1662_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1662_, 0, v___x_1661_);
    lean_ctor_set(v___x_1662_, 1, v___x_1660_);
    lean_ctor_set(v___x_1662_, 2, v___x_1659_);
    return v___x_1662_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDecl() -> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__6_once),
        _init_l_Lake_DSL_scriptDecl___closed__6,
    );
    return v___x_1663_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_DSL_DeclUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lake_DSL_packageCommand = _init_l_Lake_DSL_packageCommand();
    lean_mark_persistent(l_Lake_DSL_packageCommand);
    l_Lake_DSL_postUpdateDecl = _init_l_Lake_DSL_postUpdateDecl();
    lean_mark_persistent(l_Lake_DSL_postUpdateDecl);
    l_Lake_DSL_depName = _init_l_Lake_DSL_depName();
    lean_mark_persistent(l_Lake_DSL_depName);
    l_Lake_DSL_depSpec = _init_l_Lake_DSL_depSpec();
    lean_mark_persistent(l_Lake_DSL_depSpec);
    l_Lake_DSL_requireDecl = _init_l_Lake_DSL_requireDecl();
    lean_mark_persistent(l_Lake_DSL_requireDecl);
    l_Lake_DSL_buildDeclSig = _init_l_Lake_DSL_buildDeclSig();
    lean_mark_persistent(l_Lake_DSL_buildDeclSig);
    l_Lake_DSL_moduleFacetDecl = _init_l_Lake_DSL_moduleFacetDecl();
    lean_mark_persistent(l_Lake_DSL_moduleFacetDecl);
    l_Lake_DSL_packageFacetDecl = _init_l_Lake_DSL_packageFacetDecl();
    lean_mark_persistent(l_Lake_DSL_packageFacetDecl);
    l_Lake_DSL_libraryFacetDecl = _init_l_Lake_DSL_libraryFacetDecl();
    lean_mark_persistent(l_Lake_DSL_libraryFacetDecl);
    l_Lake_DSL_targetCommand = _init_l_Lake_DSL_targetCommand();
    lean_mark_persistent(l_Lake_DSL_targetCommand);
    l_Lake_DSL_leanLibCommand = _init_l_Lake_DSL_leanLibCommand();
    lean_mark_persistent(l_Lake_DSL_leanLibCommand);
    l_Lake_DSL_leanExeCommand = _init_l_Lake_DSL_leanExeCommand();
    lean_mark_persistent(l_Lake_DSL_leanExeCommand);
    l_Lake_DSL_inputFileCommand = _init_l_Lake_DSL_inputFileCommand();
    lean_mark_persistent(l_Lake_DSL_inputFileCommand);
    l_Lake_DSL_inputDirCommand = _init_l_Lake_DSL_inputDirCommand();
    lean_mark_persistent(l_Lake_DSL_inputDirCommand);
    l_Lake_DSL_externLibDeclSpec = _init_l_Lake_DSL_externLibDeclSpec();
    lean_mark_persistent(l_Lake_DSL_externLibDeclSpec);
    l_Lake_DSL_externLibCommand = _init_l_Lake_DSL_externLibCommand();
    lean_mark_persistent(l_Lake_DSL_externLibCommand);
    l_Lake_DSL_scriptDeclSpec = _init_l_Lake_DSL_scriptDeclSpec();
    lean_mark_persistent(l_Lake_DSL_scriptDeclSpec);
    l_Lake_DSL_scriptDecl = _init_l_Lake_DSL_scriptDecl();
    lean_mark_persistent(l_Lake_DSL_scriptDecl);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_DSL_DeclUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_DSL_Syntax(builtin);
}
