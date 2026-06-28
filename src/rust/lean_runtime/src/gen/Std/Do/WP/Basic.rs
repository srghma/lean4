// Lean compiler output
// Module: Std.Do.WP.Basic
// Imports: Std.Do.PredTrans
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Function_comp, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Do::PredTrans::{
    initialize_Std_Do_PredTrans, l_Std_Do_PredTrans_bind___redArg___lam__1,
    l_Std_Do_PredTrans_pure___boxed, l_Std_Do_PredTrans_pure___redArg___lam__0,
    l_Std_Do_PredTrans_pushArg___redArg___lam__1, l_Std_Do_PredTrans_pushExcept___redArg___lam__1,
    l_Std_Do_PredTrans_pushOption___redArg___lam__1, runtime_initialize_Std_Do_PredTrans,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value: LeanStringObject<4> =
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
        m_data: [83, 116, 100, 0],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value: LeanStringObject<3> =
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
        m_data: [68, 111, 0],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__2_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 11,
        m_data: [
            116, 101, 114, 109, 87, 112, 226, 159, 166, 95, 58, 95, 226, 159, 167, 0,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__2_value) as *mut LeanObject;
static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__2_value)
                as *mut LeanObject,
            13570875650650431554 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__4_value: LeanStringObject<8> =
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
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__4_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__4_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [119, 112, 226, 159, 166, 0],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__7_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__8_value: LeanStringObject<5> =
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
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__8_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__8_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__10_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9_value)
                as *mut LeanObject,
            (((10 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__10_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__11_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__12_value: LeanStringObject<9> =
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
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__12_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__12_value)
                as *mut LeanObject,
            18170484695678750185 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__13_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14_value: LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__15_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__15_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__16_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__9_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__16_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__17_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__18_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__18_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__19_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__19_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20_value: LeanStringObject<4> =
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
        m_data: [226, 159, 167, 0],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__21_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__21_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__22_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__19_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__21_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__22_value) as *mut LeanObject;
pub static l_Std_Do_termWp_u27e6___x3a___u27e7___closed__23_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termWp_u27e6___x3a___u27e7___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__23_value) as *mut LeanObject;
pub static mut l_Std_Do_termWp_u27e6___x3a___u27e7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__23_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__3_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__3_value) as *mut LeanObject,5353940006376281447 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__5_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__5_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__7_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__7_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__7_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__10_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__10_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__10_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__12_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__12_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13: *mut LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__15_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__14_value) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__15_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__15_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__17_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__17_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__17_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__19_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [87, 80, 46, 119, 112, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__19_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [87, 80, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [119, 112, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21_value) as *mut LeanObject,7549759810940688174 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value) as *mut LeanObject,6684006172234987772 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_termWp_u27e6___x3a___u27e7___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__21_value) as *mut LeanObject,6757038018435374033 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value) as *mut LeanObject,17511313520436183663 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__25_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__24_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__25_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__25_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__27_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__27_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__27_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__29_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__29_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__29_value) as *mut LeanObject,5346268661279150583 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33_value) as *mut LeanObject,110479913597202347 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35_value) as *mut LeanObject;
pub static l_Std_Do_unexpandWP___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__22_value) as *mut LeanObject,5372590542464025869 as *mut LeanObject] };
static mut l_Std_Do_unexpandWP___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_unexpandWP___closed__0_value) as *mut LeanObject;
static mut l_Std_Do_unexpandWP___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Do_unexpandWP___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do_Id_instWP___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Do_Id_instWP___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Do_Id_instWP___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Id_instWP___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Do_Id_instWP: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Id_instWP___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_EStateM_instWP___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Do_EStateM_instWP___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Do_EStateM_instWP___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_EStateM_instWP___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_EStateM_instWP___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Do_EStateM_instWP___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Std_Do_EStateM_instWP___closed__0_value) as *mut LeanObject],
};
static mut l_Std_Do_EStateM_instWP___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_EStateM_instWP___closed__1_value) as *mut LeanObject;
pub static l_Std_Do_State_instWP___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Do_State_instWP___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Do_State_instWP___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_State_instWP___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_Reader_instWP___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Do_Reader_instWP___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Do_Reader_instWP___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Reader_instWP___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_Except_instWP___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Do_Except_instWP___aux__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Do_Except_instWP___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Except_instWP___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_Option_instWP___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Do_Option_instWP___aux__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Do_Option_instWP___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Option_instWP___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Do_Option_instWP: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Option_instWP___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13()
-> *mut LeanObject {
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    v___x_655_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__12;
    v___x_656_ = l_String_toRawSubstring_x27(v___x_655_);
    return v___x_656_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20()
-> *mut LeanObject {
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    v___x_672_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__19;
    v___x_673_ = l_String_toRawSubstring_x27(v___x_672_);
    return v___x_673_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34()
-> *mut LeanObject {
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    v___x_702_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__33;
    v___x_703_ = l_String_toRawSubstring_x27(v___x_702_);
    return v___x_703_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1(
    mut v_x_706_: *mut LeanObject,
    mut v_a_707_: *mut LeanObject,
    mut v_a_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: u8 = 0;
    v___x_709_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3;
    lean_inc(v_x_706_);
    v___x_710_ = l_Lean_Syntax_isOfKind(v_x_706_, v___x_709_);
    if v___x_710_ == 0 {
        let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_706_);
        v___x_711_ = lean_box(1);
        v___x_712_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_712_, 0, v___x_711_);
        lean_ctor_set(v___x_712_, 1, v_a_708_);
        return v___x_712_;
    } else {
        let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_718_: u8 = 0;
        v___x_713_ = lean_unsigned_to_nat(0);
        v___x_714_ = lean_unsigned_to_nat(1);
        v___x_715_ = l_Lean_Syntax_getArg(v_x_706_, v___x_714_);
        v___x_716_ = lean_unsigned_to_nat(2);
        v___x_717_ = l_Lean_Syntax_getArg(v_x_706_, v___x_716_);
        lean_dec(v_x_706_);
        lean_inc(v___x_717_);
        v___x_718_ = l_Lean_Syntax_matchesNull(v___x_717_, v___x_713_);
        if v___x_718_ == 0 {
            let mut v___x_719_: u8 = 0;
            lean_inc(v___x_717_);
            v___x_719_ = l_Lean_Syntax_matchesNull(v___x_717_, v___x_716_);
            if v___x_719_ == 0 {
                let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_717_);
                lean_dec(v___x_715_);
                v___x_720_ = lean_box(1);
                v___x_721_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_721_, 0, v___x_720_);
                lean_ctor_set(v___x_721_, 1, v_a_708_);
                return v___x_721_;
            } else {
                let mut v_quotContext_722_: *mut LeanObject = core::ptr::null_mut();
                let mut v_currMacroScope_723_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_724_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
                v_quotContext_722_ = lean_ctor_get(v_a_707_, 1);
                v_currMacroScope_723_ = lean_ctor_get(v_a_707_, 2);
                v_ref_724_ = lean_ctor_get(v_a_707_, 5);
                v___x_725_ = l_Lean_Syntax_getArg(v___x_717_, v___x_714_);
                lean_dec(v___x_717_);
                v___x_726_ = l_Lean_SourceInfo_fromRef(v_ref_724_, v___x_718_);
                v___x_727_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4;
                v___x_728_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6;
                v___x_729_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8;
                v___x_730_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9;
                lean_inc_n(v___x_726_, 14);
                v___x_731_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_731_, 0, v___x_726_);
                lean_ctor_set(v___x_731_, 1, v___x_730_);
                v___x_732_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11;
                v___x_733_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13_once), _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13);
                v___x_734_ = lean_box(0);
                lean_inc_n(v_currMacroScope_723_, 3);
                lean_inc_n(v_quotContext_722_, 3);
                v___x_735_ =
                    l_Lean_addMacroScope(v_quotContext_722_, v___x_734_, v_currMacroScope_723_);
                v___x_736_ = lean_box(0);
                v___x_737_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16;
                v___x_738_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_738_, 0, v___x_726_);
                lean_ctor_set(v___x_738_, 1, v___x_733_);
                lean_ctor_set(v___x_738_, 2, v___x_735_);
                lean_ctor_set(v___x_738_, 3, v___x_737_);
                v___x_739_ = l_Lean_Syntax_node1(v___x_726_, v___x_732_, v___x_738_);
                v___x_740_ = l_Lean_Syntax_node2(v___x_726_, v___x_729_, v___x_731_, v___x_739_);
                v___x_741_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18;
                v___x_742_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20_once), _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20);
                v___x_743_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23;
                v___x_744_ =
                    l_Lean_addMacroScope(v_quotContext_722_, v___x_743_, v_currMacroScope_723_);
                v___x_745_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26;
                v___x_746_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_746_, 0, v___x_726_);
                lean_ctor_set(v___x_746_, 1, v___x_742_);
                lean_ctor_set(v___x_746_, 2, v___x_744_);
                lean_ctor_set(v___x_746_, 3, v___x_745_);
                v___x_747_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28;
                v___x_748_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30;
                v___x_749_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14;
                v___x_750_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_750_, 0, v___x_726_);
                lean_ctor_set(v___x_750_, 1, v___x_749_);
                v___x_751_ = l_Lean_Syntax_node1(v___x_726_, v___x_747_, v___x_725_);
                v___x_752_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31;
                v___x_753_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_753_, 0, v___x_726_);
                lean_ctor_set(v___x_753_, 1, v___x_752_);
                lean_inc_ref(v___x_753_);
                lean_inc(v___x_740_);
                v___x_754_ = l_Lean_Syntax_node5(
                    v___x_726_, v___x_748_, v___x_740_, v___x_715_, v___x_750_, v___x_751_,
                    v___x_753_,
                );
                v___x_755_ = l_Lean_Syntax_node1(v___x_726_, v___x_747_, v___x_754_);
                v___x_756_ = l_Lean_Syntax_node2(v___x_726_, v___x_741_, v___x_746_, v___x_755_);
                v___x_757_ =
                    l_Lean_Syntax_node3(v___x_726_, v___x_728_, v___x_740_, v___x_756_, v___x_753_);
                v___x_758_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32;
                v___x_759_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_759_, 0, v___x_726_);
                lean_ctor_set(v___x_759_, 1, v___x_758_);
                v___x_760_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34_once), _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34);
                v___x_761_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35;
                v___x_762_ =
                    l_Lean_addMacroScope(v_quotContext_722_, v___x_761_, v_currMacroScope_723_);
                v___x_763_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_763_, 0, v___x_726_);
                lean_ctor_set(v___x_763_, 1, v___x_760_);
                lean_ctor_set(v___x_763_, 2, v___x_762_);
                lean_ctor_set(v___x_763_, 3, v___x_736_);
                v___x_764_ =
                    l_Lean_Syntax_node3(v___x_726_, v___x_727_, v___x_757_, v___x_759_, v___x_763_);
                v___x_765_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_765_, 0, v___x_764_);
                lean_ctor_set(v___x_765_, 1, v_a_708_);
                return v___x_765_;
            }
        } else {
            let mut v_quotContext_766_: *mut LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_767_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ref_768_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_769_: u8 = 0;
            let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_717_);
            v_quotContext_766_ = lean_ctor_get(v_a_707_, 1);
            v_currMacroScope_767_ = lean_ctor_get(v_a_707_, 2);
            v_ref_768_ = lean_ctor_get(v_a_707_, 5);
            v___x_769_ = 0;
            v___x_770_ = l_Lean_SourceInfo_fromRef(v_ref_768_, v___x_769_);
            v___x_771_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__4;
            v___x_772_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__6;
            v___x_773_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8;
            v___x_774_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__9;
            lean_inc_n(v___x_770_, 11);
            v___x_775_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_775_, 0, v___x_770_);
            lean_ctor_set(v___x_775_, 1, v___x_774_);
            v___x_776_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11;
            v___x_777_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13_once), _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__13);
            v___x_778_ = lean_box(0);
            lean_inc_n(v_currMacroScope_767_, 3);
            lean_inc_n(v_quotContext_766_, 3);
            v___x_779_ =
                l_Lean_addMacroScope(v_quotContext_766_, v___x_778_, v_currMacroScope_767_);
            v___x_780_ = lean_box(0);
            v___x_781_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__16;
            v___x_782_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_782_, 0, v___x_770_);
            lean_ctor_set(v___x_782_, 1, v___x_777_);
            lean_ctor_set(v___x_782_, 2, v___x_779_);
            lean_ctor_set(v___x_782_, 3, v___x_781_);
            v___x_783_ = l_Lean_Syntax_node1(v___x_770_, v___x_776_, v___x_782_);
            v___x_784_ = l_Lean_Syntax_node2(v___x_770_, v___x_773_, v___x_775_, v___x_783_);
            v___x_785_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18;
            v___x_786_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20_once), _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__20);
            v___x_787_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__23;
            v___x_788_ =
                l_Lean_addMacroScope(v_quotContext_766_, v___x_787_, v_currMacroScope_767_);
            v___x_789_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__26;
            v___x_790_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_790_, 0, v___x_770_);
            lean_ctor_set(v___x_790_, 1, v___x_786_);
            lean_ctor_set(v___x_790_, 2, v___x_788_);
            lean_ctor_set(v___x_790_, 3, v___x_789_);
            v___x_791_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28;
            v___x_792_ = l_Lean_Syntax_node1(v___x_770_, v___x_791_, v___x_715_);
            v___x_793_ = l_Lean_Syntax_node2(v___x_770_, v___x_785_, v___x_790_, v___x_792_);
            v___x_794_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__31;
            v___x_795_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_795_, 0, v___x_770_);
            lean_ctor_set(v___x_795_, 1, v___x_794_);
            v___x_796_ =
                l_Lean_Syntax_node3(v___x_770_, v___x_772_, v___x_784_, v___x_793_, v___x_795_);
            v___x_797_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__32;
            v___x_798_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_798_, 0, v___x_770_);
            lean_ctor_set(v___x_798_, 1, v___x_797_);
            v___x_799_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34_once), _init_l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__34);
            v___x_800_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__35;
            v___x_801_ =
                l_Lean_addMacroScope(v_quotContext_766_, v___x_800_, v_currMacroScope_767_);
            v___x_802_ = lean_alloc_ctor(3, 4, (0) as u32);
            lean_ctor_set(v___x_802_, 0, v___x_770_);
            lean_ctor_set(v___x_802_, 1, v___x_799_);
            lean_ctor_set(v___x_802_, 2, v___x_801_);
            lean_ctor_set(v___x_802_, 3, v___x_780_);
            v___x_803_ =
                l_Lean_Syntax_node3(v___x_770_, v___x_771_, v___x_796_, v___x_798_, v___x_802_);
            v___x_804_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_804_, 0, v___x_803_);
            lean_ctor_set(v___x_804_, 1, v_a_708_);
            return v___x_804_;
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___boxed(
    mut v_x_805_: *mut LeanObject,
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_808_: *mut LeanObject = core::ptr::null_mut();
    v_res_808_ =
        l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1(
            v_x_805_, v_a_806_, v_a_807_,
        );
    lean_dec_ref(v_a_806_);
    return v_res_808_;
}
pub unsafe fn _init_l_Std_Do_unexpandWP___closed__1() -> *mut LeanObject {
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_811_ = l_Array_mkArray0(lean_box(0));
    return v___x_811_;
}
pub unsafe fn l_Std_Do_unexpandWP(
    mut v_x_812_: *mut LeanObject,
    mut v_a_813_: *mut LeanObject,
    mut v_a_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: u8 = 0;
    v___x_815_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__18;
    lean_inc(v_x_812_);
    v___x_816_ = l_Lean_Syntax_isOfKind(v_x_812_, v___x_815_);
    if v___x_816_ == 0 {
        let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_812_);
        v___x_817_ = lean_box(0);
        v___x_818_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_818_, 0, v___x_817_);
        lean_ctor_set(v___x_818_, 1, v_a_814_);
        return v___x_818_;
    } else {
        let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_821_: u8 = 0;
        v___x_819_ = lean_unsigned_to_nat(1);
        v___x_820_ = l_Lean_Syntax_getArg(v_x_812_, v___x_819_);
        lean_dec(v_x_812_);
        lean_inc(v___x_820_);
        v___x_821_ = l_Lean_Syntax_matchesNull(v___x_820_, v___x_819_);
        if v___x_821_ == 0 {
            let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_820_);
            v___x_822_ = lean_box(0);
            v___x_823_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_823_, 0, v___x_822_);
            lean_ctor_set(v___x_823_, 1, v_a_814_);
            return v___x_823_;
        } else {
            let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_826_: u8 = 0;
            v___x_824_ = lean_unsigned_to_nat(0);
            v___x_825_ = l_Lean_Syntax_getArg(v___x_820_, v___x_824_);
            lean_dec(v___x_820_);
            lean_inc(v___x_825_);
            v___x_826_ = l_Lean_Syntax_isOfKind(v___x_825_, v___x_815_);
            if v___x_826_ == 0 {
                let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_825_);
                v___x_827_ = lean_box(0);
                v___x_828_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_828_, 0, v___x_827_);
                lean_ctor_set(v___x_828_, 1, v_a_814_);
                return v___x_828_;
            } else {
                let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_831_: u8 = 0;
                v___x_829_ = l_Lean_Syntax_getArg(v___x_825_, v___x_824_);
                v___x_830_ = l_Std_Do_unexpandWP___closed__0;
                v___x_831_ = l_Lean_Syntax_matchesIdent(v___x_829_, v___x_830_);
                lean_dec(v___x_829_);
                if v___x_831_ == 0 {
                    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_825_);
                    v___x_832_ = lean_box(0);
                    v___x_833_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_833_, 0, v___x_832_);
                    lean_ctor_set(v___x_833_, 1, v_a_814_);
                    return v___x_833_;
                } else {
                    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_835_: u8 = 0;
                    v___x_834_ = l_Lean_Syntax_getArg(v___x_825_, v___x_819_);
                    lean_dec(v___x_825_);
                    lean_inc(v___x_834_);
                    v___x_835_ = l_Lean_Syntax_matchesNull(v___x_834_, v___x_819_);
                    if v___x_835_ == 0 {
                        let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v___x_834_);
                        v___x_836_ = lean_box(0);
                        v___x_837_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_837_, 0, v___x_836_);
                        lean_ctor_set(v___x_837_, 1, v_a_814_);
                        return v___x_837_;
                    } else {
                        let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_840_: u8 = 0;
                        v___x_838_ = l_Lean_Syntax_getArg(v___x_834_, v___x_824_);
                        lean_dec(v___x_834_);
                        v___x_839_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__30;
                        lean_inc(v___x_838_);
                        v___x_840_ = l_Lean_Syntax_isOfKind(v___x_838_, v___x_839_);
                        if v___x_840_ == 0 {
                            let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
                            v___x_841_ = l_Lean_SourceInfo_fromRef(v_a_813_, v___x_840_);
                            v___x_842_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3;
                            v___x_843_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6;
                            lean_inc_n(v___x_841_, 3);
                            v___x_844_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_844_, 0, v___x_841_);
                            lean_ctor_set(v___x_844_, 1, v___x_843_);
                            v___x_845_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28;
                            v___x_846_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Std_Do_unexpandWP___closed__1),
                                core::ptr::addr_of_mut!(l_Std_Do_unexpandWP___closed__1_once),
                                _init_l_Std_Do_unexpandWP___closed__1,
                            );
                            v___x_847_ = lean_alloc_ctor(1, 3, (0) as u32);
                            lean_ctor_set(v___x_847_, 0, v___x_841_);
                            lean_ctor_set(v___x_847_, 1, v___x_845_);
                            lean_ctor_set(v___x_847_, 2, v___x_846_);
                            v___x_848_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20;
                            v___x_849_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_849_, 0, v___x_841_);
                            lean_ctor_set(v___x_849_, 1, v___x_848_);
                            v___x_850_ = l_Lean_Syntax_node4(
                                v___x_841_, v___x_842_, v___x_844_, v___x_838_, v___x_847_,
                                v___x_849_,
                            );
                            v___x_851_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_851_, 0, v___x_850_);
                            lean_ctor_set(v___x_851_, 1, v_a_814_);
                            return v___x_851_;
                        } else {
                            let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_854_: u8 = 0;
                            v___x_852_ = l_Lean_Syntax_getArg(v___x_838_, v___x_824_);
                            v___x_853_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__8;
                            lean_inc(v___x_852_);
                            v___x_854_ = l_Lean_Syntax_isOfKind(v___x_852_, v___x_853_);
                            if v___x_854_ == 0 {
                                let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
                                lean_dec(v___x_852_);
                                v___x_855_ = l_Lean_SourceInfo_fromRef(v_a_813_, v___x_854_);
                                v___x_856_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3;
                                v___x_857_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6;
                                lean_inc_n(v___x_855_, 3);
                                v___x_858_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_858_, 0, v___x_855_);
                                lean_ctor_set(v___x_858_, 1, v___x_857_);
                                v___x_859_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28;
                                v___x_860_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Std_Do_unexpandWP___closed__1),
                                    core::ptr::addr_of_mut!(l_Std_Do_unexpandWP___closed__1_once),
                                    _init_l_Std_Do_unexpandWP___closed__1,
                                );
                                v___x_861_ = lean_alloc_ctor(1, 3, (0) as u32);
                                lean_ctor_set(v___x_861_, 0, v___x_855_);
                                lean_ctor_set(v___x_861_, 1, v___x_859_);
                                lean_ctor_set(v___x_861_, 2, v___x_860_);
                                v___x_862_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20;
                                v___x_863_ = lean_alloc_ctor(2, 2, (0) as u32);
                                lean_ctor_set(v___x_863_, 0, v___x_855_);
                                lean_ctor_set(v___x_863_, 1, v___x_862_);
                                v___x_864_ = l_Lean_Syntax_node4(
                                    v___x_855_, v___x_856_, v___x_858_, v___x_838_, v___x_861_,
                                    v___x_863_,
                                );
                                v___x_865_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_865_, 0, v___x_864_);
                                lean_ctor_set(v___x_865_, 1, v_a_814_);
                                return v___x_865_;
                            } else {
                                let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_868_: u8 = 0;
                                v___x_866_ = l_Lean_Syntax_getArg(v___x_852_, v___x_819_);
                                lean_dec(v___x_852_);
                                v___x_867_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__11;
                                lean_inc(v___x_866_);
                                v___x_868_ = l_Lean_Syntax_isOfKind(v___x_866_, v___x_867_);
                                if v___x_868_ == 0 {
                                    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
                                    lean_dec(v___x_866_);
                                    v___x_869_ = l_Lean_SourceInfo_fromRef(v_a_813_, v___x_868_);
                                    v___x_870_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3;
                                    v___x_871_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6;
                                    lean_inc_n(v___x_869_, 3);
                                    v___x_872_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_872_, 0, v___x_869_);
                                    lean_ctor_set(v___x_872_, 1, v___x_871_);
                                    v___x_873_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28;
                                    v___x_874_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(l_Std_Do_unexpandWP___closed__1),
                                        core::ptr::addr_of_mut!(
                                            l_Std_Do_unexpandWP___closed__1_once
                                        ),
                                        _init_l_Std_Do_unexpandWP___closed__1,
                                    );
                                    v___x_875_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_875_, 0, v___x_869_);
                                    lean_ctor_set(v___x_875_, 1, v___x_873_);
                                    lean_ctor_set(v___x_875_, 2, v___x_874_);
                                    v___x_876_ = l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20;
                                    v___x_877_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_877_, 0, v___x_869_);
                                    lean_ctor_set(v___x_877_, 1, v___x_876_);
                                    v___x_878_ = l_Lean_Syntax_node4(
                                        v___x_869_, v___x_870_, v___x_872_, v___x_838_, v___x_875_,
                                        v___x_877_,
                                    );
                                    v___x_879_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_879_, 0, v___x_878_);
                                    lean_ctor_set(v___x_879_, 1, v_a_814_);
                                    return v___x_879_;
                                } else {
                                    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_882_: u8 = 0;
                                    v___x_880_ = l_Lean_Syntax_getArg(v___x_866_, v___x_824_);
                                    lean_dec(v___x_866_);
                                    v___x_881_ = lean_box(0);
                                    v___x_882_ = l_Lean_Syntax_matchesIdent(v___x_880_, v___x_881_);
                                    lean_dec(v___x_880_);
                                    if v___x_882_ == 0 {
                                        let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
                                        v___x_883_ =
                                            l_Lean_SourceInfo_fromRef(v_a_813_, v___x_882_);
                                        v___x_884_ =
                                            l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3;
                                        v___x_885_ =
                                            l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6;
                                        lean_inc_n(v___x_883_, 3);
                                        v___x_886_ = lean_alloc_ctor(2, 2, (0) as u32);
                                        lean_ctor_set(v___x_886_, 0, v___x_883_);
                                        lean_ctor_set(v___x_886_, 1, v___x_885_);
                                        v___x_887_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28;
                                        v___x_888_ = lean_obj_once(
                                            core::ptr::addr_of_mut!(
                                                l_Std_Do_unexpandWP___closed__1
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Std_Do_unexpandWP___closed__1_once
                                            ),
                                            _init_l_Std_Do_unexpandWP___closed__1,
                                        );
                                        v___x_889_ = lean_alloc_ctor(1, 3, (0) as u32);
                                        lean_ctor_set(v___x_889_, 0, v___x_883_);
                                        lean_ctor_set(v___x_889_, 1, v___x_887_);
                                        lean_ctor_set(v___x_889_, 2, v___x_888_);
                                        v___x_890_ =
                                            l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20;
                                        v___x_891_ = lean_alloc_ctor(2, 2, (0) as u32);
                                        lean_ctor_set(v___x_891_, 0, v___x_883_);
                                        lean_ctor_set(v___x_891_, 1, v___x_890_);
                                        v___x_892_ = l_Lean_Syntax_node4(
                                            v___x_883_, v___x_884_, v___x_886_, v___x_838_,
                                            v___x_889_, v___x_891_,
                                        );
                                        v___x_893_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_893_, 0, v___x_892_);
                                        lean_ctor_set(v___x_893_, 1, v_a_814_);
                                        return v___x_893_;
                                    } else {
                                        let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
                                        let mut v___x_896_: u8 = 0;
                                        v___x_894_ = lean_unsigned_to_nat(3);
                                        v___x_895_ = l_Lean_Syntax_getArg(v___x_838_, v___x_894_);
                                        lean_inc(v___x_895_);
                                        v___x_896_ =
                                            l_Lean_Syntax_matchesNull(v___x_895_, v___x_819_);
                                        if v___x_896_ == 0 {
                                            let mut v___x_897_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_898_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_899_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_900_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_901_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_902_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_903_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_904_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_905_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_906_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_907_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            lean_dec(v___x_895_);
                                            v___x_897_ =
                                                l_Lean_SourceInfo_fromRef(v_a_813_, v___x_896_);
                                            v___x_898_ =
                                                l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3;
                                            v___x_899_ =
                                                l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6;
                                            lean_inc_n(v___x_897_, 3);
                                            v___x_900_ = lean_alloc_ctor(2, 2, (0) as u32);
                                            lean_ctor_set(v___x_900_, 0, v___x_897_);
                                            lean_ctor_set(v___x_900_, 1, v___x_899_);
                                            v___x_901_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28;
                                            v___x_902_ = lean_obj_once(
                                                core::ptr::addr_of_mut!(
                                                    l_Std_Do_unexpandWP___closed__1
                                                ),
                                                core::ptr::addr_of_mut!(
                                                    l_Std_Do_unexpandWP___closed__1_once
                                                ),
                                                _init_l_Std_Do_unexpandWP___closed__1,
                                            );
                                            v___x_903_ = lean_alloc_ctor(1, 3, (0) as u32);
                                            lean_ctor_set(v___x_903_, 0, v___x_897_);
                                            lean_ctor_set(v___x_903_, 1, v___x_901_);
                                            lean_ctor_set(v___x_903_, 2, v___x_902_);
                                            v___x_904_ =
                                                l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20;
                                            v___x_905_ = lean_alloc_ctor(2, 2, (0) as u32);
                                            lean_ctor_set(v___x_905_, 0, v___x_897_);
                                            lean_ctor_set(v___x_905_, 1, v___x_904_);
                                            v___x_906_ = l_Lean_Syntax_node4(
                                                v___x_897_, v___x_898_, v___x_900_, v___x_838_,
                                                v___x_903_, v___x_905_,
                                            );
                                            v___x_907_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v___x_907_, 0, v___x_906_);
                                            lean_ctor_set(v___x_907_, 1, v_a_814_);
                                            return v___x_907_;
                                        } else {
                                            let mut v___x_908_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_909_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_910_: u8 = 0;
                                            let mut v___x_911_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_912_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_913_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_914_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_915_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_916_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_917_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_918_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_919_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_920_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_921_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_922_: *mut LeanObject =
                                                core::ptr::null_mut();
                                            v___x_908_ =
                                                l_Lean_Syntax_getArg(v___x_838_, v___x_819_);
                                            lean_dec(v___x_838_);
                                            v___x_909_ =
                                                l_Lean_Syntax_getArg(v___x_895_, v___x_824_);
                                            lean_dec(v___x_895_);
                                            v___x_910_ = 0;
                                            v___x_911_ =
                                                l_Lean_SourceInfo_fromRef(v_a_813_, v___x_910_);
                                            v___x_912_ =
                                                l_Std_Do_termWp_u27e6___x3a___u27e7___closed__3;
                                            v___x_913_ =
                                                l_Std_Do_termWp_u27e6___x3a___u27e7___closed__6;
                                            lean_inc_n(v___x_911_, 4);
                                            v___x_914_ = lean_alloc_ctor(2, 2, (0) as u32);
                                            lean_ctor_set(v___x_914_, 0, v___x_911_);
                                            lean_ctor_set(v___x_914_, 1, v___x_913_);
                                            v___x_915_ = l_Std_Do___aux__Std__Do__WP__Basic______macroRules__Std__Do__termWp_u27e6___x3a___u27e7__1___closed__28;
                                            v___x_916_ =
                                                l_Std_Do_termWp_u27e6___x3a___u27e7___closed__14;
                                            v___x_917_ = lean_alloc_ctor(2, 2, (0) as u32);
                                            lean_ctor_set(v___x_917_, 0, v___x_911_);
                                            lean_ctor_set(v___x_917_, 1, v___x_916_);
                                            v___x_918_ = l_Lean_Syntax_node2(
                                                v___x_911_, v___x_915_, v___x_917_, v___x_909_,
                                            );
                                            v___x_919_ =
                                                l_Std_Do_termWp_u27e6___x3a___u27e7___closed__20;
                                            v___x_920_ = lean_alloc_ctor(2, 2, (0) as u32);
                                            lean_ctor_set(v___x_920_, 0, v___x_911_);
                                            lean_ctor_set(v___x_920_, 1, v___x_919_);
                                            v___x_921_ = l_Lean_Syntax_node4(
                                                v___x_911_, v___x_912_, v___x_914_, v___x_908_,
                                                v___x_918_, v___x_920_,
                                            );
                                            v___x_922_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v___x_922_, 0, v___x_921_);
                                            lean_ctor_set(v___x_922_, 1, v_a_814_);
                                            return v___x_922_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Do_unexpandWP___boxed(
    mut v_x_923_: *mut LeanObject,
    mut v_a_924_: *mut LeanObject,
    mut v_a_925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_926_: *mut LeanObject = core::ptr::null_mut();
    v_res_926_ = l_Std_Do_unexpandWP(v_x_923_, v_a_924_, v_a_925_);
    lean_dec(v_a_924_);
    return v_res_926_;
}
pub unsafe fn l_Std_Do_Id_instWP___lam__0(
    mut v_00_u03b1_927_: *mut LeanObject,
    mut v_x_928_: *mut LeanObject,
    mut v___y_929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    v___x_930_ = l_Std_Do_PredTrans_pure___redArg___lam__0(v_x_928_, v___y_929_);
    return v___x_930_;
}
pub unsafe fn l_Std_Do_StateT_instWP___redArg___lam__0(
    mut v_x_933_: *mut LeanObject,
    mut v_inst_934_: *mut LeanObject,
    mut v_s_935_: *mut LeanObject,
    mut v___y_936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    v___x_937_ = lean_apply_1(v_x_933_, v_s_935_);
    v___x_938_ = lean_apply_3(v_inst_934_, lean_box(0), v___x_937_, v___y_936_);
    return v___x_938_;
}
pub unsafe fn l_Std_Do_StateT_instWP___redArg___lam__1(
    mut v_inst_939_: *mut LeanObject,
    mut v_00_u03b1_940_: *mut LeanObject,
    mut v_x_941_: *mut LeanObject,
    mut v___y_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    v___f_943_ = lean_alloc_closure(
        l_Std_Do_StateT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_943_, 0, v_x_941_);
    lean_closure_set(v___f_943_, 1, v_inst_939_);
    v___x_944_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_944_, 0, v___f_943_);
    lean_closure_set(v___x_944_, 1, v___y_942_);
    return v___x_944_;
}
pub unsafe fn l_Std_Do_StateT_instWP___redArg(mut v_inst_945_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_946_: *mut LeanObject = core::ptr::null_mut();
    v___f_946_ = lean_alloc_closure(
        l_Std_Do_StateT_instWP___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_946_, 0, v_inst_945_);
    return v___f_946_;
}
pub unsafe fn l_Std_Do_StateT_instWP(
    mut v_m_947_: *mut LeanObject,
    mut v_ps_948_: *mut LeanObject,
    mut v_00_u03c3_949_: *mut LeanObject,
    mut v_inst_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_951_: *mut LeanObject = core::ptr::null_mut();
    v___f_951_ = lean_alloc_closure(
        l_Std_Do_StateT_instWP___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_951_, 0, v_inst_950_);
    return v___f_951_;
}
pub unsafe fn l_Std_Do_StateT_instWP___boxed(
    mut v_m_952_: *mut LeanObject,
    mut v_ps_953_: *mut LeanObject,
    mut v_00_u03c3_954_: *mut LeanObject,
    mut v_inst_955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_956_: *mut LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Std_Do_StateT_instWP(v_m_952_, v_ps_953_, v_00_u03c3_954_, v_inst_955_);
    lean_dec(v_ps_953_);
    return v_res_956_;
}
pub unsafe fn l_Std_Do_ReaderT_instWP___redArg___lam__0(
    mut v_s_957_: *mut LeanObject,
    mut v_x_958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    v___x_959_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_959_, 0, v_x_958_);
    lean_ctor_set(v___x_959_, 1, v_s_957_);
    return v___x_959_;
}
pub unsafe fn l_Std_Do_ReaderT_instWP___redArg___lam__1(
    mut v_x_960_: *mut LeanObject,
    mut v_inst_961_: *mut LeanObject,
    mut v_ps_962_: *mut LeanObject,
    mut v_s_963_: *mut LeanObject,
    mut v___y_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_963_);
    v___f_965_ = lean_alloc_closure(
        l_Std_Do_ReaderT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_965_, 0, v_s_963_);
    v___x_966_ = lean_apply_1(v_x_960_, v_s_963_);
    v___x_967_ = lean_apply_2(v_inst_961_, lean_box(0), v___x_966_);
    v___x_968_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_968_, 0, v_ps_962_);
    lean_closure_set(v___x_968_, 1, lean_box(0));
    v___x_969_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_969_, 0, lean_box(0));
    lean_closure_set(v___x_969_, 1, lean_box(0));
    lean_closure_set(v___x_969_, 2, lean_box(0));
    lean_closure_set(v___x_969_, 3, v___x_968_);
    lean_closure_set(v___x_969_, 4, v___f_965_);
    v___x_970_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_969_, v___x_967_, v___y_964_);
    return v___x_970_;
}
pub unsafe fn l_Std_Do_ReaderT_instWP___redArg___lam__2(
    mut v_inst_971_: *mut LeanObject,
    mut v_ps_972_: *mut LeanObject,
    mut v_00_u03b1_973_: *mut LeanObject,
    mut v_x_974_: *mut LeanObject,
    mut v___y_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    v___f_976_ = lean_alloc_closure(
        l_Std_Do_ReaderT_instWP___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_976_, 0, v_x_974_);
    lean_closure_set(v___f_976_, 1, v_inst_971_);
    lean_closure_set(v___f_976_, 2, v_ps_972_);
    v___x_977_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_977_, 0, v___f_976_);
    lean_closure_set(v___x_977_, 1, v___y_975_);
    return v___x_977_;
}
pub unsafe fn l_Std_Do_ReaderT_instWP___redArg(
    mut v_ps_978_: *mut LeanObject,
    mut v_inst_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_980_: *mut LeanObject = core::ptr::null_mut();
    v___f_980_ = lean_alloc_closure(
        l_Std_Do_ReaderT_instWP___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_980_, 0, v_inst_979_);
    lean_closure_set(v___f_980_, 1, v_ps_978_);
    return v___f_980_;
}
pub unsafe fn l_Std_Do_ReaderT_instWP(
    mut v_m_981_: *mut LeanObject,
    mut v_ps_982_: *mut LeanObject,
    mut v_00_u03c1_983_: *mut LeanObject,
    mut v_inst_984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_985_: *mut LeanObject = core::ptr::null_mut();
    v___f_985_ = lean_alloc_closure(
        l_Std_Do_ReaderT_instWP___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_985_, 0, v_inst_984_);
    lean_closure_set(v___f_985_, 1, v_ps_982_);
    return v___f_985_;
}
pub unsafe fn l_Std_Do_ExceptT_instWP___redArg___lam__0(
    mut v_inst_986_: *mut LeanObject,
    mut v_00_u03b1_987_: *mut LeanObject,
    mut v_x_988_: *mut LeanObject,
    mut v___y_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    v___x_990_ = lean_apply_2(v_inst_986_, lean_box(0), v_x_988_);
    v___x_991_ = l_Std_Do_PredTrans_pushExcept___redArg___lam__1(v___x_990_, v___y_989_);
    return v___x_991_;
}
pub unsafe fn l_Std_Do_ExceptT_instWP___redArg(
    mut v_inst_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_993_: *mut LeanObject = core::ptr::null_mut();
    v___f_993_ = lean_alloc_closure(
        l_Std_Do_ExceptT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_993_, 0, v_inst_992_);
    return v___f_993_;
}
pub unsafe fn l_Std_Do_ExceptT_instWP(
    mut v_m_994_: *mut LeanObject,
    mut v_ps_995_: *mut LeanObject,
    mut v_00_u03b5_996_: *mut LeanObject,
    mut v_inst_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_998_: *mut LeanObject = core::ptr::null_mut();
    v___f_998_ = lean_alloc_closure(
        l_Std_Do_ExceptT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_998_, 0, v_inst_997_);
    return v___f_998_;
}
pub unsafe fn l_Std_Do_ExceptT_instWP___boxed(
    mut v_m_999_: *mut LeanObject,
    mut v_ps_1000_: *mut LeanObject,
    mut v_00_u03b5_1001_: *mut LeanObject,
    mut v_inst_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1003_: *mut LeanObject = core::ptr::null_mut();
    v_res_1003_ = l_Std_Do_ExceptT_instWP(v_m_999_, v_ps_1000_, v_00_u03b5_1001_, v_inst_1002_);
    lean_dec(v_ps_1000_);
    return v_res_1003_;
}
pub unsafe fn l_Std_Do_OptionT_instWP___redArg___lam__0(
    mut v_inst_1004_: *mut LeanObject,
    mut v_00_u03b1_1005_: *mut LeanObject,
    mut v_x_1006_: *mut LeanObject,
    mut v___y_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    v___x_1008_ = lean_apply_2(v_inst_1004_, lean_box(0), v_x_1006_);
    v___x_1009_ = l_Std_Do_PredTrans_pushOption___redArg___lam__1(v___x_1008_, v___y_1007_);
    return v___x_1009_;
}
pub unsafe fn l_Std_Do_OptionT_instWP___redArg(
    mut v_inst_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1011_: *mut LeanObject = core::ptr::null_mut();
    v___f_1011_ = lean_alloc_closure(
        l_Std_Do_OptionT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1011_, 0, v_inst_1010_);
    return v___f_1011_;
}
pub unsafe fn l_Std_Do_OptionT_instWP(
    mut v_m_1012_: *mut LeanObject,
    mut v_ps_1013_: *mut LeanObject,
    mut v_inst_1014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1015_: *mut LeanObject = core::ptr::null_mut();
    v___f_1015_ = lean_alloc_closure(
        l_Std_Do_OptionT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1015_, 0, v_inst_1014_);
    return v___f_1015_;
}
pub unsafe fn l_Std_Do_OptionT_instWP___boxed(
    mut v_m_1016_: *mut LeanObject,
    mut v_ps_1017_: *mut LeanObject,
    mut v_inst_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1019_: *mut LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Std_Do_OptionT_instWP(v_m_1016_, v_ps_1017_, v_inst_1018_);
    lean_dec(v_ps_1017_);
    return v_res_1019_;
}
pub unsafe fn l_Std_Do_EStateM_instWP___lam__0(
    mut v___y_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    v___x_1021_ = lean_box(0);
    return v___x_1021_;
}
pub unsafe fn l_Std_Do_EStateM_instWP___lam__0___boxed(
    mut v___y_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1023_: *mut LeanObject = core::ptr::null_mut();
    v_res_1023_ = l_Std_Do_EStateM_instWP___lam__0(v___y_1022_);
    lean_dec(v___y_1022_);
    return v_res_1023_;
}
pub unsafe fn l_Std_Do_EStateM_instWP___lam__1(
    mut v___f_1024_: *mut LeanObject,
    mut v_00_u03b1_1025_: *mut LeanObject,
    mut v_x_1026_: *mut LeanObject,
    mut v___y_1027_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___f_1024_);
    return v___f_1024_;
}
pub unsafe fn l_Std_Do_EStateM_instWP___lam__1___boxed(
    mut v___f_1028_: *mut LeanObject,
    mut v_00_u03b1_1029_: *mut LeanObject,
    mut v_x_1030_: *mut LeanObject,
    mut v___y_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1032_: *mut LeanObject = core::ptr::null_mut();
    v_res_1032_ =
        l_Std_Do_EStateM_instWP___lam__1(v___f_1028_, v_00_u03b1_1029_, v_x_1030_, v___y_1031_);
    lean_dec_ref(v___y_1031_);
    lean_dec_ref(v_x_1030_);
    lean_dec_ref(v___f_1028_);
    return v_res_1032_;
}
pub unsafe fn l_Std_Do_EStateM_instWP(
    mut v_00_u03b5_1036_: *mut LeanObject,
    mut v_00_u03c3_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1038_: *mut LeanObject = core::ptr::null_mut();
    v___f_1038_ = l_Std_Do_EStateM_instWP___closed__1;
    return v___f_1038_;
}
pub unsafe fn l_Std_Do_State_instWP___lam__0(
    mut v_x_1039_: *mut LeanObject,
    mut v_s_1040_: *mut LeanObject,
    mut v___y_1041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1042_ = lean_apply_1(v_x_1039_, v_s_1040_);
    v___x_1043_ = l_Std_Do_PredTrans_pure___redArg___lam__0(v___x_1042_, v___y_1041_);
    return v___x_1043_;
}
pub unsafe fn l_Std_Do_State_instWP___lam__1(
    mut v_00_u03b1_1044_: *mut LeanObject,
    mut v_x_1045_: *mut LeanObject,
    mut v___y_1046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    v___f_1047_ = lean_alloc_closure(
        l_Std_Do_State_instWP___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1047_, 0, v_x_1045_);
    v___x_1048_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_1048_, 0, v___f_1047_);
    lean_closure_set(v___x_1048_, 1, v___y_1046_);
    return v___x_1048_;
}
pub unsafe fn l_Std_Do_State_instWP(mut v_00_u03c3_1050_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1051_: *mut LeanObject = core::ptr::null_mut();
    v___f_1051_ = l_Std_Do_State_instWP___closed__0;
    return v___f_1051_;
}
pub unsafe fn l_Std_Do_Reader_instWP___lam__1(
    mut v_x_1052_: *mut LeanObject,
    mut v___x_1053_: *mut LeanObject,
    mut v_s_1054_: *mut LeanObject,
    mut v___y_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_1054_);
    v___f_1056_ = lean_alloc_closure(
        l_Std_Do_ReaderT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1056_, 0, v_s_1054_);
    v___x_1057_ = lean_apply_1(v_x_1052_, v_s_1054_);
    v___f_1058_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1058_, 0, v___x_1057_);
    v___x_1059_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_1059_, 0, v___x_1053_);
    lean_closure_set(v___x_1059_, 1, lean_box(0));
    v___x_1060_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_1060_, 0, lean_box(0));
    lean_closure_set(v___x_1060_, 1, lean_box(0));
    lean_closure_set(v___x_1060_, 2, lean_box(0));
    lean_closure_set(v___x_1060_, 3, v___x_1059_);
    lean_closure_set(v___x_1060_, 4, v___f_1056_);
    v___x_1061_ = l_Std_Do_PredTrans_bind___redArg___lam__1(v___x_1060_, v___f_1058_, v___y_1055_);
    return v___x_1061_;
}
pub unsafe fn l_Std_Do_Reader_instWP___lam__0(
    mut v___x_1062_: *mut LeanObject,
    mut v_00_u03b1_1063_: *mut LeanObject,
    mut v_x_1064_: *mut LeanObject,
    mut v___y_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___f_1066_ = lean_alloc_closure(
        l_Std_Do_Reader_instWP___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1066_, 0, v_x_1064_);
    lean_closure_set(v___f_1066_, 1, v___x_1062_);
    v___x_1067_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_1067_, 0, v___f_1066_);
    lean_closure_set(v___x_1067_, 1, v___y_1065_);
    return v___x_1067_;
}
pub unsafe fn l_Std_Do_Reader_instWP(mut v_00_u03c1_1070_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1071_: *mut LeanObject = core::ptr::null_mut();
    v___f_1071_ = l_Std_Do_Reader_instWP___closed__0;
    return v___f_1071_;
}
pub unsafe fn l_Std_Do_Except_instWP___aux__1___redArg(
    mut v_x_1072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1074_: *mut LeanObject = core::ptr::null_mut();
    v___f_1073_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1073_, 0, v_x_1072_);
    v___f_1074_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1074_, 0, v___f_1073_);
    return v___f_1074_;
}
pub unsafe fn l_Std_Do_Except_instWP___aux__1(
    mut v_00_u03b5_1075_: *mut LeanObject,
    mut v_00_u03b1_1076_: *mut LeanObject,
    mut v_x_1077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1079_: *mut LeanObject = core::ptr::null_mut();
    v___f_1078_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1078_, 0, v_x_1077_);
    v___f_1079_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1079_, 0, v___f_1078_);
    return v___f_1079_;
}
pub unsafe fn l_Std_Do_Except_instWP(mut v_00_u03b5_1081_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    v___x_1082_ = l_Std_Do_Except_instWP___closed__0;
    return v___x_1082_;
}
pub unsafe fn l_Std_Do_Option_instWP___aux__1___redArg(
    mut v_x_1083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1085_: *mut LeanObject = core::ptr::null_mut();
    v___f_1084_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1084_, 0, v_x_1083_);
    v___f_1085_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1085_, 0, v___f_1084_);
    return v___f_1085_;
}
pub unsafe fn l_Std_Do_Option_instWP___aux__1(
    mut v_00_u03b1_1086_: *mut LeanObject,
    mut v_x_1087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1089_: *mut LeanObject = core::ptr::null_mut();
    v___f_1088_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pure___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1088_, 0, v_x_1087_);
    v___f_1089_ = lean_alloc_closure(
        l_Std_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1089_, 0, v___f_1088_);
    return v___f_1089_;
}
pub unsafe fn l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(
    mut v_x_1092_: *mut LeanObject,
    mut v_h__1_1093_: *mut LeanObject,
    mut v_h__2_1094_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1092_) == 0 {
        let mut v_a_1095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1093_);
        v_a_1095_ = lean_ctor_get(v_x_1092_, 0);
        lean_inc(v_a_1095_);
        lean_dec_ref_known(v_x_1092_, 1);
        v___x_1096_ = lean_apply_1(v_h__2_1094_, v_a_1095_);
        return v___x_1096_;
    } else {
        let mut v_a_1097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1094_);
        v_a_1097_ = lean_ctor_get(v_x_1092_, 0);
        lean_inc(v_a_1097_);
        lean_dec_ref_known(v_x_1092_, 1);
        v___x_1098_ = lean_apply_1(v_h__1_1093_, v_a_1097_);
        return v___x_1098_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushExcept_match__1_splitter(
    mut v_00_u03b1_1099_: *mut LeanObject,
    mut v_00_u03b5_1100_: *mut LeanObject,
    mut v_motive_1101_: *mut LeanObject,
    mut v_x_1102_: *mut LeanObject,
    mut v_h__1_1103_: *mut LeanObject,
    mut v_h__2_1104_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1102_) == 0 {
        let mut v_a_1105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1103_);
        v_a_1105_ = lean_ctor_get(v_x_1102_, 0);
        lean_inc(v_a_1105_);
        lean_dec_ref_known(v_x_1102_, 1);
        v___x_1106_ = lean_apply_1(v_h__2_1104_, v_a_1105_);
        return v___x_1106_;
    } else {
        let mut v_a_1107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1104_);
        v_a_1107_ = lean_ctor_get(v_x_1102_, 0);
        lean_inc(v_a_1107_);
        lean_dec_ref_known(v_x_1102_, 1);
        v___x_1108_ = lean_apply_1(v_h__1_1103_, v_a_1107_);
        return v___x_1108_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(
    mut v_x_1109_: *mut LeanObject,
    mut v_h__1_1110_: *mut LeanObject,
    mut v_h__2_1111_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1109_) == 0 {
        let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1110_);
        v___x_1112_ = lean_box(0);
        v___x_1113_ = lean_apply_1(v_h__2_1111_, v___x_1112_);
        return v___x_1113_;
    } else {
        let mut v_val_1114_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1111_);
        v_val_1114_ = lean_ctor_get(v_x_1109_, 0);
        lean_inc(v_val_1114_);
        lean_dec_ref_known(v_x_1109_, 1);
        v___x_1115_ = lean_apply_1(v_h__1_1110_, v_val_1114_);
        return v___x_1115_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Basic_0__Std_Do_PredTrans_pushOption_match__1_splitter(
    mut v_00_u03b1_1116_: *mut LeanObject,
    mut v_motive_1117_: *mut LeanObject,
    mut v_x_1118_: *mut LeanObject,
    mut v_h__1_1119_: *mut LeanObject,
    mut v_h__2_1120_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1118_) == 0 {
        let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1119_);
        v___x_1121_ = lean_box(0);
        v___x_1122_ = lean_apply_1(v_h__2_1120_, v___x_1121_);
        return v___x_1122_;
    } else {
        let mut v_val_1123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1120_);
        v_val_1123_ = lean_ctor_get(v_x_1118_, 0);
        lean_inc(v_val_1123_);
        lean_dec_ref_known(v_x_1118_, 1);
        v___x_1124_ = lean_apply_1(v_h__1_1119_, v_val_1123_);
        return v___x_1124_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Basic_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(
    mut v_x_1125_: *mut LeanObject,
    mut v_h__1_1126_: *mut LeanObject,
    mut v_h__2_1127_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1125_) == 0 {
        let mut v_a_1128_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1127_);
        v_a_1128_ = lean_ctor_get(v_x_1125_, 0);
        lean_inc(v_a_1128_);
        v_a_1129_ = lean_ctor_get(v_x_1125_, 1);
        lean_inc(v_a_1129_);
        lean_dec_ref_known(v_x_1125_, 2);
        v___x_1130_ = lean_apply_2(v_h__1_1126_, v_a_1128_, v_a_1129_);
        return v___x_1130_;
    } else {
        let mut v_a_1131_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1126_);
        v_a_1131_ = lean_ctor_get(v_x_1125_, 0);
        lean_inc(v_a_1131_);
        v_a_1132_ = lean_ctor_get(v_x_1125_, 1);
        lean_inc(v_a_1132_);
        lean_dec_ref_known(v_x_1125_, 2);
        v___x_1133_ = lean_apply_2(v_h__2_1127_, v_a_1131_, v_a_1132_);
        return v___x_1133_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Basic_0__Std_Do_EStateM_instWP_match__1_splitter(
    mut v_00_u03b5_1134_: *mut LeanObject,
    mut v_00_u03c3_1135_: *mut LeanObject,
    mut v_00_u03b1_1136_: *mut LeanObject,
    mut v_motive_1137_: *mut LeanObject,
    mut v_x_1138_: *mut LeanObject,
    mut v_h__1_1139_: *mut LeanObject,
    mut v_h__2_1140_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1138_) == 0 {
        let mut v_a_1141_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1140_);
        v_a_1141_ = lean_ctor_get(v_x_1138_, 0);
        lean_inc(v_a_1141_);
        v_a_1142_ = lean_ctor_get(v_x_1138_, 1);
        lean_inc(v_a_1142_);
        lean_dec_ref_known(v_x_1138_, 2);
        v___x_1143_ = lean_apply_2(v_h__1_1139_, v_a_1141_, v_a_1142_);
        return v___x_1143_;
    } else {
        let mut v_a_1144_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1139_);
        v_a_1144_ = lean_ctor_get(v_x_1138_, 0);
        lean_inc(v_a_1144_);
        v_a_1145_ = lean_ctor_get(v_x_1138_, 1);
        lean_inc(v_a_1145_);
        lean_dec_ref_known(v_x_1138_, 2);
        v___x_1146_ = lean_apply_2(v_h__2_1140_, v_a_1144_, v_a_1145_);
        return v___x_1146_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_WP_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_PredTrans(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_WP_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_WP_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_PredTrans(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_WP_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Do_WP_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Do_WP_Basic(builtin);
}
