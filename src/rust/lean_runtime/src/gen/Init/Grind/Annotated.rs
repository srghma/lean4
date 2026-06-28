// Lean compiler output
// Module: Init.Grind.Annotated
// Imports: Init.Notation
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub static l_Lean_Parser_Command_grindAnnotated___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Command_grindAnnotated___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Parser_Command_grindAnnotated___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__2_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Command_grindAnnotated___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__3_value: LeanStringObject<15> =
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
            103, 114, 105, 110, 100, 65, 110, 110, 111, 116, 97, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Parser_Command_grindAnnotated___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__3_value) as *mut LeanObject;
static l_Lean_Parser_Command_grindAnnotated___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_grindAnnotated___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_grindAnnotated___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_grindAnnotated___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__3_value)
                as *mut LeanObject,
            10959305042798744005 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_grindAnnotated___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__5_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Command_grindAnnotated___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__5_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_grindAnnotated___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__7_value: LeanStringObject<16> =
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
            103, 114, 105, 110, 100, 95, 97, 110, 110, 111, 116, 97, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Parser_Command_grindAnnotated___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__8_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_grindAnnotated___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__9_value: LeanStringObject<4> =
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
static mut l_Lean_Parser_Command_grindAnnotated___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__9_value)
                as *mut LeanObject,
            9232979286016572671 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_grindAnnotated___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_grindAnnotated___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_grindAnnotated___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Command_grindAnnotated___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__4_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_grindAnnotated___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__13_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Command_grindAnnotated: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindAnnotated___closed__13_value) as *mut LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Annotated(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn meta_initialize_Init_Grind_Annotated(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Annotated(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Grind_Annotated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Annotated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Annotated(builtin);
}
