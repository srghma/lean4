// Lean compiler output
// Module: Std.Internal.Do.Triple.Basic
// Imports: Std.Internal.Do.WP
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Internal::Do::WP::{
    initialize_Std_Internal_Do_WP, runtime_initialize_Std_Internal_Do_WP,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_once, lean_unsigned_to_nat,
};
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
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
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 11,
    m_data: [
        116, 101, 114, 109, 226, 166, 131, 95, 226, 166, 132, 95, 226, 166, 131, 95, 226, 166, 132,
        0,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value)
        as *mut LeanObject;
static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_1:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value)
            as *mut LeanObject,
        1742885236933170401 as *mut LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_2:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value)
            as *mut LeanObject,
        1237304041707523237 as *mut LeanObject,
    ],
};
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value: LeanCtorObject<
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value)
            as *mut LeanObject,
        14221277149122107325 as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value:
    LeanStringObject<8> = LeanStringObject {
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
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value)
            as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [226, 166, 131, 32, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value: LeanCtorObject<
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
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value:
    LeanStringObject<5> = LeanStringObject {
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
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value)
            as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 166, 132, 32, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value: LeanCtorObject<
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
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 166, 131, 32, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value: LeanCtorObject<
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
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [32, 226, 166, 132, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value: LeanCtorObject<
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
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value)
            as *mut LeanObject,
        (((60 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value)
        as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value) as *mut LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value) as *mut LeanObject,12441331751180145720 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value) as *mut LeanObject,1742885236933170401 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value) as *mut LeanObject,1237304041707523237 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value) as *mut LeanObject,9297738788347984318 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 114, 100, 101, 114, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 5, m_data: [116, 101, 114, 109, 226, 138, 165, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value) as *mut LeanObject,14079511657030373096 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 138, 165, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1_value) as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 13,
    m_data: [
        116, 101, 114, 109, 226, 166, 131, 95, 226, 166, 132, 95, 226, 166, 131, 95, 44, 95, 226,
        166, 132, 0,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value
)
    as *mut LeanObject;
static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_1:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value)
            as *mut LeanObject,
        1742885236933170401 as *mut LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_2:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value)
            as *mut LeanObject,
        1237304041707523237 as *mut LeanObject,
    ],
};
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value
        ) as *mut LeanObject,
        14703663799162239584 as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value
)
    as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value
)
    as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value
)
    as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value)
            as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value
)
    as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value
)
    as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value
)
    as *mut LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value
        ) as *mut LeanObject,
        (((60 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value
)
    as *mut LeanObject;
pub static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value
)
    as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7_value) as *mut LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8: *mut LeanObject = core::ptr::null_mut();
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value) as *mut LeanObject,1742885236933170401 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value) as *mut LeanObject,1237304041707523237 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value) as *mut LeanObject,489434913524309295 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value) as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value) as *mut LeanObject,7043493786777132025 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value) as *mut LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value) as *mut LeanObject,16077784126176397009 as *mut LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value) as *mut LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20_value) as *mut LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6()
-> *mut LeanObject {
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v___x_475_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5;
    v___x_476_ = l_String_toRawSubstring_x27(v___x_475_);
    return v___x_476_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(
    mut v_x_505_: *mut LeanObject,
    mut v_a_506_: *mut LeanObject,
    mut v_a_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: u8 = 0;
    v___x_508_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4;
    lean_inc(v_x_505_);
    v___x_509_ = l_Lean_Syntax_isOfKind(v_x_505_, v___x_508_);
    if v___x_509_ == 0 {
        let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_505_);
        v___x_510_ = lean_box(1);
        v___x_511_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_511_, 0, v___x_510_);
        lean_ctor_set(v___x_511_, 1, v_a_507_);
        return v___x_511_;
    } else {
        let mut v_quotContext_512_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_513_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_521_: u8 = 0;
        let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_512_ = lean_ctor_get(v_a_506_, 1);
        v_currMacroScope_513_ = lean_ctor_get(v_a_506_, 2);
        v_ref_514_ = lean_ctor_get(v_a_506_, 5);
        v___x_515_ = lean_unsigned_to_nat(1);
        v___x_516_ = l_Lean_Syntax_getArg(v_x_505_, v___x_515_);
        v___x_517_ = lean_unsigned_to_nat(3);
        v___x_518_ = l_Lean_Syntax_getArg(v_x_505_, v___x_517_);
        v___x_519_ = lean_unsigned_to_nat(5);
        v___x_520_ = l_Lean_Syntax_getArg(v_x_505_, v___x_519_);
        lean_dec(v_x_505_);
        v___x_521_ = 0;
        v___x_522_ = l_Lean_SourceInfo_fromRef(v_ref_514_, v___x_521_);
        v___x_523_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
        v___x_524_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
        v___x_525_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7;
        lean_inc(v_currMacroScope_513_);
        lean_inc(v_quotContext_512_);
        v___x_526_ = l_Lean_addMacroScope(v_quotContext_512_, v___x_525_, v_currMacroScope_513_);
        v___x_527_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12;
        lean_inc_n(v___x_522_, 4);
        v___x_528_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_528_, 0, v___x_522_);
        lean_ctor_set(v___x_528_, 1, v___x_524_);
        lean_ctor_set(v___x_528_, 2, v___x_526_);
        lean_ctor_set(v___x_528_, 3, v___x_527_);
        v___x_529_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14;
        v___x_530_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
        v___x_531_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18;
        v___x_532_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_532_, 0, v___x_522_);
        lean_ctor_set(v___x_532_, 1, v___x_531_);
        v___x_533_ = l_Lean_Syntax_node1(v___x_522_, v___x_530_, v___x_532_);
        v___x_534_ = l_Lean_Syntax_node4(
            v___x_522_, v___x_529_, v___x_516_, v___x_518_, v___x_520_, v___x_533_,
        );
        v___x_535_ = l_Lean_Syntax_node2(v___x_522_, v___x_523_, v___x_528_, v___x_534_);
        v___x_536_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_536_, 0, v___x_535_);
        lean_ctor_set(v___x_536_, 1, v_a_507_);
        return v___x_536_;
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___boxed(
    mut v_x_537_: *mut LeanObject,
    mut v_a_538_: *mut LeanObject,
    mut v_a_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_540_: *mut LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(v_x_537_, v_a_538_, v_a_539_);
    lean_dec_ref(v_a_538_);
    return v_res_540_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(
    mut v_x_544_: *mut LeanObject,
    mut v_a_545_: *mut LeanObject,
    mut v_a_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: u8 = 0;
    v___x_547_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
    lean_inc(v_x_544_);
    v___x_548_ = l_Lean_Syntax_isOfKind(v_x_544_, v___x_547_);
    if v___x_548_ == 0 {
        let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_544_);
        v___x_549_ = lean_box(0);
        v___x_550_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_550_, 0, v___x_549_);
        lean_ctor_set(v___x_550_, 1, v_a_546_);
        return v___x_550_;
    } else {
        let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_554_: u8 = 0;
        v___x_551_ = lean_unsigned_to_nat(0);
        v___x_552_ = l_Lean_Syntax_getArg(v_x_544_, v___x_551_);
        v___x_553_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1;
        lean_inc(v___x_552_);
        v___x_554_ = l_Lean_Syntax_isOfKind(v___x_552_, v___x_553_);
        if v___x_554_ == 0 {
            let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_552_);
            lean_dec(v_x_544_);
            v___x_555_ = lean_box(0);
            v___x_556_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_556_, 0, v___x_555_);
            lean_ctor_set(v___x_556_, 1, v_a_546_);
            return v___x_556_;
        } else {
            let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_560_: u8 = 0;
            v___x_557_ = lean_unsigned_to_nat(1);
            v___x_558_ = l_Lean_Syntax_getArg(v_x_544_, v___x_557_);
            lean_dec(v_x_544_);
            v___x_559_ = lean_unsigned_to_nat(4);
            lean_inc(v___x_558_);
            v___x_560_ = l_Lean_Syntax_matchesNull(v___x_558_, v___x_559_);
            if v___x_560_ == 0 {
                let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_558_);
                lean_dec(v___x_552_);
                v___x_561_ = lean_box(0);
                v___x_562_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_562_, 0, v___x_561_);
                lean_ctor_set(v___x_562_, 1, v_a_546_);
                return v___x_562_;
            } else {
                let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_566_: u8 = 0;
                v___x_563_ = lean_unsigned_to_nat(3);
                v___x_564_ = l_Lean_Syntax_getArg(v___x_558_, v___x_563_);
                v___x_565_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
                v___x_566_ = l_Lean_Syntax_isOfKind(v___x_564_, v___x_565_);
                if v___x_566_ == 0 {
                    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_558_);
                    lean_dec(v___x_552_);
                    v___x_567_ = lean_box(0);
                    v___x_568_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_568_, 0, v___x_567_);
                    lean_ctor_set(v___x_568_, 1, v_a_546_);
                    return v___x_568_;
                } else {
                    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_ref_573_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_574_: u8 = 0;
                    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
                    v___x_569_ = l_Lean_Syntax_getArg(v___x_558_, v___x_551_);
                    v___x_570_ = l_Lean_Syntax_getArg(v___x_558_, v___x_557_);
                    v___x_571_ = lean_unsigned_to_nat(2);
                    v___x_572_ = l_Lean_Syntax_getArg(v___x_558_, v___x_571_);
                    lean_dec(v___x_558_);
                    v_ref_573_ = l_Lean_replaceRef(v___x_552_, v_a_545_);
                    lean_dec(v___x_552_);
                    v___x_574_ = 0;
                    v___x_575_ = l_Lean_SourceInfo_fromRef(v_ref_573_, v___x_574_);
                    lean_dec(v_ref_573_);
                    v___x_576_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4;
                    v___x_577_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7;
                    lean_inc_n(v___x_575_, 4);
                    v___x_578_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_578_, 0, v___x_575_);
                    lean_ctor_set(v___x_578_, 1, v___x_577_);
                    v___x_579_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13;
                    v___x_580_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_580_, 0, v___x_575_);
                    lean_ctor_set(v___x_580_, 1, v___x_579_);
                    v___x_581_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17;
                    v___x_582_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_582_, 0, v___x_575_);
                    lean_ctor_set(v___x_582_, 1, v___x_581_);
                    v___x_583_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21;
                    v___x_584_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_584_, 0, v___x_575_);
                    lean_ctor_set(v___x_584_, 1, v___x_583_);
                    v___x_585_ = l_Lean_Syntax_node7(
                        v___x_575_, v___x_576_, v___x_578_, v___x_569_, v___x_580_, v___x_570_,
                        v___x_582_, v___x_572_, v___x_584_,
                    );
                    v___x_586_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_586_, 0, v___x_585_);
                    lean_ctor_set(v___x_586_, 1, v_a_546_);
                    return v___x_586_;
                }
            }
        }
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___boxed(
    mut v_x_587_: *mut LeanObject,
    mut v_a_588_: *mut LeanObject,
    mut v_a_589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_590_: *mut LeanObject = core::ptr::null_mut();
    v_res_590_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(v_x_587_, v_a_588_, v_a_589_);
    lean_dec(v_a_588_);
    return v_res_590_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8()
-> *mut LeanObject {
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    v___x_634_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7;
    v___x_635_ = l_String_toRawSubstring_x27(v___x_634_);
    return v___x_635_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19()
-> *mut LeanObject {
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    v___x_665_ = l_Array_mkArray0(lean_box(0));
    return v___x_665_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(
    mut v_x_668_: *mut LeanObject,
    mut v_a_669_: *mut LeanObject,
    mut v_a_670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    v___x_671_ = l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1;
    lean_inc(v_x_668_);
    v___x_672_ = l_Lean_Syntax_isOfKind(v_x_668_, v___x_671_);
    if v___x_672_ == 0 {
        let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_668_);
        v___x_673_ = lean_box(1);
        v___x_674_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_674_, 0, v___x_673_);
        lean_ctor_set(v___x_674_, 1, v_a_670_);
        return v___x_674_;
    } else {
        let mut v_quotContext_675_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_676_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_686_: u8 = 0;
        let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_675_ = lean_ctor_get(v_a_669_, 1);
        v_currMacroScope_676_ = lean_ctor_get(v_a_669_, 2);
        v_ref_677_ = lean_ctor_get(v_a_669_, 5);
        v___x_678_ = lean_unsigned_to_nat(1);
        v___x_679_ = l_Lean_Syntax_getArg(v_x_668_, v___x_678_);
        v___x_680_ = lean_unsigned_to_nat(3);
        v___x_681_ = l_Lean_Syntax_getArg(v_x_668_, v___x_680_);
        v___x_682_ = lean_unsigned_to_nat(5);
        v___x_683_ = l_Lean_Syntax_getArg(v_x_668_, v___x_682_);
        v___x_684_ = lean_unsigned_to_nat(7);
        v___x_685_ = l_Lean_Syntax_getArg(v_x_668_, v___x_684_);
        lean_dec(v_x_668_);
        v___x_686_ = 0;
        v___x_687_ = l_Lean_SourceInfo_fromRef(v_ref_677_, v___x_686_);
        v___x_688_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
        v___x_689_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
        v___x_690_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7;
        lean_inc_n(v_currMacroScope_676_, 2);
        lean_inc_n(v_quotContext_675_, 2);
        v___x_691_ = l_Lean_addMacroScope(v_quotContext_675_, v___x_690_, v_currMacroScope_676_);
        v___x_692_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12;
        lean_inc_n(v___x_687_, 16);
        v___x_693_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_693_, 0, v___x_687_);
        lean_ctor_set(v___x_693_, 1, v___x_689_);
        lean_ctor_set(v___x_693_, 2, v___x_691_);
        lean_ctor_set(v___x_693_, 3, v___x_692_);
        v___x_694_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14;
        v___x_695_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1;
        v___x_696_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3;
        v___x_697_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4;
        v___x_698_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_698_, 0, v___x_687_);
        lean_ctor_set(v___x_698_, 1, v___x_697_);
        v___x_699_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6;
        v___x_700_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8);
        v___x_701_ = lean_box(0);
        v___x_702_ = l_Lean_addMacroScope(v_quotContext_675_, v___x_701_, v_currMacroScope_676_);
        v___x_703_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14;
        v___x_704_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_704_, 0, v___x_687_);
        lean_ctor_set(v___x_704_, 1, v___x_700_);
        lean_ctor_set(v___x_704_, 2, v___x_702_);
        lean_ctor_set(v___x_704_, 3, v___x_703_);
        v___x_705_ = l_Lean_Syntax_node1(v___x_687_, v___x_699_, v___x_704_);
        v___x_706_ = l_Lean_Syntax_node2(v___x_687_, v___x_696_, v___x_698_, v___x_705_);
        v___x_707_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15;
        v___x_708_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16;
        v___x_709_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_709_, 0, v___x_687_);
        lean_ctor_set(v___x_709_, 1, v___x_707_);
        v___x_710_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18;
        v___x_711_ = l_Lean_Syntax_node1(v___x_687_, v___x_694_, v___x_683_);
        v___x_712_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19);
        v___x_713_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_713_, 0, v___x_687_);
        lean_ctor_set(v___x_713_, 1, v___x_694_);
        lean_ctor_set(v___x_713_, 2, v___x_712_);
        v___x_714_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20;
        v___x_715_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_715_, 0, v___x_687_);
        lean_ctor_set(v___x_715_, 1, v___x_714_);
        v___x_716_ = l_Lean_Syntax_node4(
            v___x_687_, v___x_710_, v___x_711_, v___x_713_, v___x_715_, v___x_685_,
        );
        v___x_717_ = l_Lean_Syntax_node2(v___x_687_, v___x_708_, v___x_709_, v___x_716_);
        v___x_718_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21;
        v___x_719_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_719_, 0, v___x_687_);
        lean_ctor_set(v___x_719_, 1, v___x_718_);
        v___x_720_ =
            l_Lean_Syntax_node3(v___x_687_, v___x_695_, v___x_706_, v___x_717_, v___x_719_);
        v___x_721_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
        v___x_722_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18;
        v___x_723_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_723_, 0, v___x_687_);
        lean_ctor_set(v___x_723_, 1, v___x_722_);
        v___x_724_ = l_Lean_Syntax_node1(v___x_687_, v___x_721_, v___x_723_);
        v___x_725_ = l_Lean_Syntax_node4(
            v___x_687_, v___x_694_, v___x_679_, v___x_681_, v___x_720_, v___x_724_,
        );
        v___x_726_ = l_Lean_Syntax_node2(v___x_687_, v___x_688_, v___x_693_, v___x_725_);
        v___x_727_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_727_, 0, v___x_726_);
        lean_ctor_set(v___x_727_, 1, v_a_670_);
        return v___x_727_;
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___boxed(
    mut v_x_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
    mut v_a_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_731_: *mut LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(v_x_728_, v_a_729_, v_a_730_);
    lean_dec_ref(v_a_729_);
    return v_res_731_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(
    mut v_x_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
    mut v_a_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    v___x_735_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
    lean_inc(v_x_732_);
    v___x_736_ = l_Lean_Syntax_isOfKind(v_x_732_, v___x_735_);
    if v___x_736_ == 0 {
        let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_732_);
        v___x_737_ = lean_box(0);
        v___x_738_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_738_, 0, v___x_737_);
        lean_ctor_set(v___x_738_, 1, v_a_734_);
        return v___x_738_;
    } else {
        let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_742_: u8 = 0;
        v___x_739_ = lean_unsigned_to_nat(0);
        v___x_740_ = l_Lean_Syntax_getArg(v_x_732_, v___x_739_);
        v___x_741_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1;
        lean_inc(v___x_740_);
        v___x_742_ = l_Lean_Syntax_isOfKind(v___x_740_, v___x_741_);
        if v___x_742_ == 0 {
            let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_740_);
            lean_dec(v_x_732_);
            v___x_743_ = lean_box(0);
            v___x_744_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_744_, 0, v___x_743_);
            lean_ctor_set(v___x_744_, 1, v_a_734_);
            return v___x_744_;
        } else {
            let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_748_: u8 = 0;
            v___x_745_ = lean_unsigned_to_nat(1);
            v___x_746_ = l_Lean_Syntax_getArg(v_x_732_, v___x_745_);
            lean_dec(v_x_732_);
            v___x_747_ = lean_unsigned_to_nat(4);
            lean_inc(v___x_746_);
            v___x_748_ = l_Lean_Syntax_matchesNull(v___x_746_, v___x_747_);
            if v___x_748_ == 0 {
                let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_746_);
                lean_dec(v___x_740_);
                v___x_749_ = lean_box(0);
                v___x_750_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_750_, 0, v___x_749_);
                lean_ctor_set(v___x_750_, 1, v_a_734_);
                return v___x_750_;
            } else {
                let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_754_: u8 = 0;
                v___x_751_ = lean_unsigned_to_nat(2);
                v___x_752_ = l_Lean_Syntax_getArg(v___x_746_, v___x_751_);
                v___x_753_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16;
                lean_inc(v___x_752_);
                v___x_754_ = l_Lean_Syntax_isOfKind(v___x_752_, v___x_753_);
                if v___x_754_ == 0 {
                    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_752_);
                    lean_dec(v___x_746_);
                    lean_dec(v___x_740_);
                    v___x_755_ = lean_box(0);
                    v___x_756_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_756_, 0, v___x_755_);
                    lean_ctor_set(v___x_756_, 1, v_a_734_);
                    return v___x_756_;
                } else {
                    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_759_: u8 = 0;
                    v___x_757_ = l_Lean_Syntax_getArg(v___x_752_, v___x_745_);
                    lean_dec(v___x_752_);
                    v___x_758_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18;
                    lean_inc(v___x_757_);
                    v___x_759_ = l_Lean_Syntax_isOfKind(v___x_757_, v___x_758_);
                    if v___x_759_ == 0 {
                        let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v___x_757_);
                        lean_dec(v___x_746_);
                        lean_dec(v___x_740_);
                        v___x_760_ = lean_box(0);
                        v___x_761_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_761_, 0, v___x_760_);
                        lean_ctor_set(v___x_761_, 1, v_a_734_);
                        return v___x_761_;
                    } else {
                        let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_763_: u8 = 0;
                        v___x_762_ = l_Lean_Syntax_getArg(v___x_757_, v___x_739_);
                        lean_inc(v___x_762_);
                        v___x_763_ = l_Lean_Syntax_matchesNull(v___x_762_, v___x_745_);
                        if v___x_763_ == 0 {
                            let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v___x_762_);
                            lean_dec(v___x_757_);
                            lean_dec(v___x_746_);
                            lean_dec(v___x_740_);
                            v___x_764_ = lean_box(0);
                            v___x_765_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_765_, 0, v___x_764_);
                            lean_ctor_set(v___x_765_, 1, v_a_734_);
                            return v___x_765_;
                        } else {
                            let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_767_: u8 = 0;
                            v___x_766_ = l_Lean_Syntax_getArg(v___x_757_, v___x_745_);
                            v___x_767_ = l_Lean_Syntax_matchesNull(v___x_766_, v___x_739_);
                            if v___x_767_ == 0 {
                                let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
                                lean_dec(v___x_762_);
                                lean_dec(v___x_757_);
                                lean_dec(v___x_746_);
                                lean_dec(v___x_740_);
                                v___x_768_ = lean_box(0);
                                v___x_769_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_769_, 0, v___x_768_);
                                lean_ctor_set(v___x_769_, 1, v_a_734_);
                                return v___x_769_;
                            } else {
                                let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_773_: u8 = 0;
                                v___x_770_ = lean_unsigned_to_nat(3);
                                v___x_771_ = l_Lean_Syntax_getArg(v___x_746_, v___x_770_);
                                v___x_772_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
                                v___x_773_ = l_Lean_Syntax_isOfKind(v___x_771_, v___x_772_);
                                if v___x_773_ == 0 {
                                    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
                                    lean_dec(v___x_762_);
                                    lean_dec(v___x_757_);
                                    lean_dec(v___x_746_);
                                    lean_dec(v___x_740_);
                                    v___x_774_ = lean_box(0);
                                    v___x_775_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_775_, 0, v___x_774_);
                                    lean_ctor_set(v___x_775_, 1, v_a_734_);
                                    return v___x_775_;
                                } else {
                                    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v_ref_780_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_781_: u8 = 0;
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
                                    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
                                    v___x_776_ = l_Lean_Syntax_getArg(v___x_746_, v___x_739_);
                                    v___x_777_ = l_Lean_Syntax_getArg(v___x_746_, v___x_745_);
                                    lean_dec(v___x_746_);
                                    v___x_778_ = l_Lean_Syntax_getArg(v___x_762_, v___x_739_);
                                    lean_dec(v___x_762_);
                                    v___x_779_ = l_Lean_Syntax_getArg(v___x_757_, v___x_770_);
                                    lean_dec(v___x_757_);
                                    v_ref_780_ = l_Lean_replaceRef(v___x_740_, v_a_733_);
                                    lean_dec(v___x_740_);
                                    v___x_781_ = 0;
                                    v___x_782_ = l_Lean_SourceInfo_fromRef(v_ref_780_, v___x_781_);
                                    lean_dec(v_ref_780_);
                                    v___x_783_ = l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1;
                                    v___x_784_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7;
                                    lean_inc_n(v___x_782_, 5);
                                    v___x_785_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_785_, 0, v___x_782_);
                                    lean_ctor_set(v___x_785_, 1, v___x_784_);
                                    v___x_786_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13;
                                    v___x_787_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_787_, 0, v___x_782_);
                                    lean_ctor_set(v___x_787_, 1, v___x_786_);
                                    v___x_788_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17;
                                    v___x_789_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_789_, 0, v___x_782_);
                                    lean_ctor_set(v___x_789_, 1, v___x_788_);
                                    v___x_790_ = l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2;
                                    v___x_791_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_791_, 0, v___x_782_);
                                    lean_ctor_set(v___x_791_, 1, v___x_790_);
                                    v___x_792_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21;
                                    v___x_793_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_793_, 0, v___x_782_);
                                    lean_ctor_set(v___x_793_, 1, v___x_792_);
                                    v___x_794_ = lean_unsigned_to_nat(9);
                                    v___x_795_ = lean_mk_empty_array_with_capacity(v___x_794_);
                                    v___x_796_ = lean_array_push(v___x_795_, v___x_785_);
                                    v___x_797_ = lean_array_push(v___x_796_, v___x_776_);
                                    v___x_798_ = lean_array_push(v___x_797_, v___x_787_);
                                    v___x_799_ = lean_array_push(v___x_798_, v___x_777_);
                                    v___x_800_ = lean_array_push(v___x_799_, v___x_789_);
                                    v___x_801_ = lean_array_push(v___x_800_, v___x_778_);
                                    v___x_802_ = lean_array_push(v___x_801_, v___x_791_);
                                    v___x_803_ = lean_array_push(v___x_802_, v___x_779_);
                                    v___x_804_ = lean_array_push(v___x_803_, v___x_793_);
                                    v___x_805_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_805_, 0, v___x_782_);
                                    lean_ctor_set(v___x_805_, 1, v___x_783_);
                                    lean_ctor_set(v___x_805_, 2, v___x_804_);
                                    v___x_806_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_806_, 0, v___x_805_);
                                    lean_ctor_set(v___x_806_, 1, v_a_734_);
                                    return v___x_806_;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2___boxed(
    mut v_x_807_: *mut LeanObject,
    mut v_a_808_: *mut LeanObject,
    mut v_a_809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_810_: *mut LeanObject = core::ptr::null_mut();
    v_res_810_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(v_x_807_, v_a_808_, v_a_809_);
    lean_dec(v_a_808_);
    return v_res_810_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_Triple_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_WP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_Triple_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_Do_Triple_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_WP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_Triple_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Internal_Do_Triple_Basic(builtin);
}
