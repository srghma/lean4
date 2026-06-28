// Lean compiler output
// Module: Init.Core
// Imports: Init.SizeOf Init.Tactics
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::SizeOf::{initialize_Init_SizeOf, runtime_initialize_Init_SizeOf};
use crate::r#gen::Init::Tactics::{initialize_Init_Tactics, runtime_initialize_Init_Tactics};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_thunkCoe___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_thunkCoe___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_thunkCoe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_thunkCoe___closed__0_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 101, 114, 109, 95, 60, 45, 62, 95, 0],
};
static mut l_term___x3c_x2d_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__0_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__0_value) as *mut LeanObject,
        8663684876064120238 as *mut LeanObject,
    ],
};
static mut l_term___x3c_x2d_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__1_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__2_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_term___x3c_x2d_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__2_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_term___x3c_x2d_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__4_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 60, 45, 62, 32, 0],
};
static mut l_term___x3c_x2d_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__4_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__4_value) as *mut LeanObject],
};
static mut l_term___x3c_x2d_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__5_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__6_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_term___x3c_x2d_x3e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__6_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__6_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_term___x3c_x2d_x3e___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__7_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__7_value) as *mut LeanObject,
        (((21 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x2d_x3e___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__8_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__8_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x2d_x3e___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__9_value) as *mut LeanObject;
pub static l_term___x3c_x2d_x3e___00__closed__10_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__1_value) as *mut LeanObject,
        (((20 as usize) << 1) | 1) as *mut LeanObject,
        (((21 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__9_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x2d_x3e___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__10_value) as *mut LeanObject;
pub static mut l_term___x3c_x2d_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__10_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
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
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__3_value:
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
    m_data: [97, 112, 112, 0],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__3_value
) as *mut LeanObject;
static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_1:
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
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_2:
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
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value:
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
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__3_value
        ) as *mut LeanObject,
        12966880221525079621 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5_value:
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
    m_data: [73, 102, 102, 0],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5_value
) as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5_value
        ) as *mut LeanObject,
        9917798623386220051 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__8_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__8_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__9_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7_value
    ) as *mut LeanObject],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__9_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__10_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__9_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__10_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__10_value
        ) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__12_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__12_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__12_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13_value
) as *mut LeanObject;
pub static l___aux__Init__Core______unexpand__Iff__1___closed__0_value: LeanStringObject<6> =
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
static mut l___aux__Init__Core______unexpand__Iff__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______unexpand__Iff__1___closed__0_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______unexpand__Iff__1___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l___aux__Init__Core______unexpand__Iff__1___closed__0_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l___aux__Init__Core______unexpand__Iff__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______unexpand__Iff__1___closed__1_value)
        as *mut LeanObject;
pub static l_term___u2194___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 134, 148, 95, 0],
};
static mut l_term___u2194___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2194___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2194___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2194___00__closed__0_value) as *mut LeanObject,
        17648941618195692764 as *mut LeanObject,
    ],
};
static mut l_term___u2194___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2194___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2194___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 134, 148, 32, 0],
};
static mut l_term___u2194___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2194___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2194___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2194___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2194___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2194___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2194___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2194___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__8_value) as *mut LeanObject,
    ],
};
static mut l_term___u2194___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2194___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2194___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2194___00__closed__1_value) as *mut LeanObject,
        (((20 as usize) << 1) | 1) as *mut LeanObject,
        (((21 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2194___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2194___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2194___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___u2194__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2194___00__closed__5_value) as *mut LeanObject;
pub static l_term___u2295___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 138, 149, 95, 0],
};
static mut l_term___u2295___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2295___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2295___00__closed__0_value) as *mut LeanObject,
        12891558494857819647 as *mut LeanObject,
    ],
};
static mut l_term___u2295___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2295___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 138, 149, 32, 0],
};
static mut l_term___u2295___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2295___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2295___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2295___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2295___00__closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__7_value) as *mut LeanObject,
        (((30 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term___u2295___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2295___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2295___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2295___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2295___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295___00__closed__5_value) as *mut LeanObject;
pub static l_term___u2295___00__closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2295___00__closed__1_value) as *mut LeanObject,
        (((30 as usize) << 1) | 1) as *mut LeanObject,
        (((31 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2295___00__closed__5_value) as *mut LeanObject,
    ],
};
static mut l_term___u2295___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295___00__closed__6_value) as *mut LeanObject;
pub static mut l_term___u2295__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295___00__closed__6_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295____1___closed__0_value:
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
    m_data: [83, 117, 109, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2295____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2295____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u2295____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___u2295____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u2295____1___closed__2_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295____1___closed__0_value
        ) as *mut LeanObject,
        5855732725875895033 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2295____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2295____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295____1___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295____1___closed__2_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2295____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2295____1___closed__3_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295____1___closed__4_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___aux__Init__Core______macroRules__term___u2295____1___closed__2_value
    ) as *mut LeanObject],
};
static mut l___aux__Init__Core______macroRules__term___u2295____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2295____1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295____1___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295____1___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2295____1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2295____1___closed__5_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295____1___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295____1___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295____1___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2295____1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2295____1___closed__6_value)
        as *mut LeanObject;
pub static l_term___u2295_x27___00__closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 8,
    m_data: [116, 101, 114, 109, 95, 226, 138, 149, 39, 95, 0],
};
static mut l_term___u2295_x27___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295_x27___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2295_x27___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2295_x27___00__closed__0_value) as *mut LeanObject,
        10964767159777112173 as *mut LeanObject,
    ],
};
static mut l_term___u2295_x27___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295_x27___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2295_x27___00__closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 4,
    m_data: [32, 226, 138, 149, 39, 32, 0],
};
static mut l_term___u2295_x27___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295_x27___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2295_x27___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2295_x27___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2295_x27___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295_x27___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2295_x27___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2295_x27___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2295___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2295_x27___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295_x27___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2295_x27___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2295_x27___00__closed__1_value) as *mut LeanObject,
        (((30 as usize) << 1) | 1) as *mut LeanObject,
        (((31 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2295_x27___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2295_x27___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295_x27___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___u2295_x27__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2295_x27___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0_value:
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
    m_data: [80, 83, 117, 109, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0_value
)
    as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0_value
        ) as *mut LeanObject,
        3874814940683362451 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2_value
)
    as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__3_value
)
    as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__4_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2_value
    ) as *mut LeanObject],
};
static mut l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__4_value
)
    as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__5_value
)
    as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6: *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6_value
)
    as *mut LeanObject;
pub static l_term___u2248___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 137, 136, 95, 0],
};
static mut l_term___u2248___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2248___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2248___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2248___00__closed__0_value) as *mut LeanObject,
        4230892755522833305 as *mut LeanObject,
    ],
};
static mut l_term___u2248___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2248___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2248___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 137, 136, 32, 0],
};
static mut l_term___u2248___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2248___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2248___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2248___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2248___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2248___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2248___00__closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__7_value) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term___u2248___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2248___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2248___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2248___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2248___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2248___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2248___00__closed__5_value) as *mut LeanObject;
pub static l_term___u2248___00__closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2248___00__closed__1_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2248___00__closed__5_value) as *mut LeanObject,
    ],
};
static mut l_term___u2248___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2248___00__closed__6_value) as *mut LeanObject;
pub static mut l_term___u2248__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2248___00__closed__6_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2248____1___closed__0_value:
    LeanStringObject<15> = LeanStringObject {
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
        72, 97, 115, 69, 113, 117, 105, 118, 46, 69, 113, 117, 105, 118, 0,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2248____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2248____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u2248____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___u2248____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u2248____1___closed__2_value:
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
    m_data: [72, 97, 115, 69, 113, 117, 105, 118, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2248____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2248____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2248____1___closed__3_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [69, 113, 117, 105, 118, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2248____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2248____1___closed__3_value)
        as *mut LeanObject;
static l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2248____1___closed__2_value
        ) as *mut LeanObject,
        14733285342191348596 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value:
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
            l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2248____1___closed__3_value
        ) as *mut LeanObject,
        10763959399715361659 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2248____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2248____1___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2248____1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2248____1___closed__5_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2248____1___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2248____1___closed__5_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2248____1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2248____1___closed__6_value)
        as *mut LeanObject;
pub static l_term___u2286___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 138, 134, 95, 0],
};
static mut l_term___u2286___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2286___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2286___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2286___00__closed__0_value) as *mut LeanObject,
        5176406056088816145 as *mut LeanObject,
    ],
};
static mut l_term___u2286___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2286___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2286___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 138, 134, 32, 0],
};
static mut l_term___u2286___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2286___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2286___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2286___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2286___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2286___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2286___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2286___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2248___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2286___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2286___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2286___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2286___00__closed__1_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2286___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2286___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2286___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___u2286__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2286___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2286____1___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [83, 117, 98, 115, 101, 116, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2286____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2286____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u2286____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___u2286____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u2286____1___closed__2_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2286____1___closed__0_value
        ) as *mut LeanObject,
        8987441732284207693 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2286____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2286____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2286____1___closed__3_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [72, 97, 115, 83, 117, 98, 115, 101, 116, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2286____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2286____1___closed__3_value)
        as *mut LeanObject;
static l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2286____1___closed__3_value
        ) as *mut LeanObject,
        15426211522887548266 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value:
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
            l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2286____1___closed__0_value
        ) as *mut LeanObject,
        6694872273224513704 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2286____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2286____1___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2286____1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2286____1___closed__5_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2286____1___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2286____1___closed__5_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2286____1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2286____1___closed__6_value)
        as *mut LeanObject;
pub static l_term___u2282___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 138, 130, 95, 0],
};
static mut l_term___u2282___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2282___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2282___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2282___00__closed__0_value) as *mut LeanObject,
        6590347383071581352 as *mut LeanObject,
    ],
};
static mut l_term___u2282___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2282___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2282___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 138, 130, 32, 0],
};
static mut l_term___u2282___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2282___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2282___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2282___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2282___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2282___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2282___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2282___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2248___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2282___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2282___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2282___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2282___00__closed__1_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2282___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2282___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2282___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___u2282__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2282___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2282____1___closed__0_value:
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
    m_data: [83, 83, 117, 98, 115, 101, 116, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2282____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2282____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u2282____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___u2282____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u2282____1___closed__2_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2282____1___closed__0_value
        ) as *mut LeanObject,
        11395855095045842192 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2282____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2282____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2282____1___closed__3_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [72, 97, 115, 83, 83, 117, 98, 115, 101, 116, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2282____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2282____1___closed__3_value)
        as *mut LeanObject;
static l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2282____1___closed__3_value
        ) as *mut LeanObject,
        1579823003328320506 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value:
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
            l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2282____1___closed__0_value
        ) as *mut LeanObject,
        4182282279141014117 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2282____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2282____1___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2282____1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2282____1___closed__5_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2282____1___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2282____1___closed__5_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2282____1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2282____1___closed__6_value)
        as *mut LeanObject;
pub static l_term___u2287___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 138, 135, 95, 0],
};
static mut l_term___u2287___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2287___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2287___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2287___00__closed__0_value) as *mut LeanObject,
        8374780288282734718 as *mut LeanObject,
    ],
};
static mut l_term___u2287___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2287___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2287___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 138, 135, 32, 0],
};
static mut l_term___u2287___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2287___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2287___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2287___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2287___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2287___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2287___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2287___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2248___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2287___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2287___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2287___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2287___00__closed__1_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2287___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2287___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2287___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___u2287__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2287___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2287____1___closed__0_value:
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
    m_data: [83, 117, 112, 101, 114, 115, 101, 116, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2287____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2287____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u2287____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___u2287____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u2287____1___closed__2_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2287____1___closed__0_value
        ) as *mut LeanObject,
        13864603907032524307 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2287____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2287____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2287____1___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2287____1___closed__2_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2287____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2287____1___closed__3_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2287____1___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2287____1___closed__3_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2287____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2287____1___closed__4_value)
        as *mut LeanObject;
pub static l_term___u2283___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 138, 131, 95, 0],
};
static mut l_term___u2283___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2283___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2283___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2283___00__closed__0_value) as *mut LeanObject,
        2941378491569920306 as *mut LeanObject,
    ],
};
static mut l_term___u2283___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2283___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2283___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 138, 131, 32, 0],
};
static mut l_term___u2283___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2283___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2283___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2283___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2283___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2283___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2283___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2283___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2248___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2283___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2283___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2283___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2283___00__closed__1_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2283___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2283___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2283___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___u2283__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2283___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2283____1___closed__0_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [83, 83, 117, 112, 101, 114, 115, 101, 116, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2283____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2283____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u2283____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___u2283____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u2283____1___closed__2_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2283____1___closed__0_value
        ) as *mut LeanObject,
        17965690073652219089 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2283____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2283____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2283____1___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2283____1___closed__2_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2283____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2283____1___closed__3_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2283____1___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2283____1___closed__3_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2283____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2283____1___closed__4_value)
        as *mut LeanObject;
pub static l_term___u222a___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 136, 170, 95, 0],
};
static mut l_term___u222a___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u222a___00__closed__0_value) as *mut LeanObject;
pub static l_term___u222a___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u222a___00__closed__0_value) as *mut LeanObject,
        9021099732844258506 as *mut LeanObject,
    ],
};
static mut l_term___u222a___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u222a___00__closed__1_value) as *mut LeanObject;
pub static l_term___u222a___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 136, 170, 32, 0],
};
static mut l_term___u222a___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u222a___00__closed__2_value) as *mut LeanObject;
pub static l_term___u222a___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u222a___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u222a___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u222a___00__closed__3_value) as *mut LeanObject;
pub static l_term___u222a___00__closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__7_value) as *mut LeanObject,
        (((66 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term___u222a___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u222a___00__closed__4_value) as *mut LeanObject;
pub static l_term___u222a___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u222a___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u222a___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u222a___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u222a___00__closed__5_value) as *mut LeanObject;
pub static l_term___u222a___00__closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u222a___00__closed__1_value) as *mut LeanObject,
        (((65 as usize) << 1) | 1) as *mut LeanObject,
        (((65 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u222a___00__closed__5_value) as *mut LeanObject,
    ],
};
static mut l_term___u222a___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term___u222a___00__closed__6_value) as *mut LeanObject;
pub static mut l_term___u222a__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u222a___00__closed__6_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u222a____1___closed__0_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [85, 110, 105, 111, 110, 46, 117, 110, 105, 111, 110, 0],
};
static mut l___aux__Init__Core______macroRules__term___u222a____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u222a____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u222a____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___u222a____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u222a____1___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [85, 110, 105, 111, 110, 0],
};
static mut l___aux__Init__Core______macroRules__term___u222a____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u222a____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u222a____1___closed__3_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [117, 110, 105, 111, 110, 0],
};
static mut l___aux__Init__Core______macroRules__term___u222a____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u222a____1___closed__3_value)
        as *mut LeanObject;
static l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u222a____1___closed__2_value
        ) as *mut LeanObject,
        4547824540083351698 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value:
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
            l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u222a____1___closed__3_value
        ) as *mut LeanObject,
        14895945545999640806 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u222a____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u222a____1___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u222a____1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u222a____1___closed__5_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u222a____1___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u222a____1___closed__5_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u222a____1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u222a____1___closed__6_value)
        as *mut LeanObject;
pub static l_term___u2229___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 136, 169, 95, 0],
};
static mut l_term___u2229___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2229___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2229___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2229___00__closed__0_value) as *mut LeanObject,
        7146945053882715602 as *mut LeanObject,
    ],
};
static mut l_term___u2229___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2229___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2229___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 136, 169, 32, 0],
};
static mut l_term___u2229___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2229___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2229___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2229___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2229___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2229___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2229___00__closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__7_value) as *mut LeanObject,
        (((71 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term___u2229___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2229___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2229___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2229___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2229___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2229___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2229___00__closed__5_value) as *mut LeanObject;
pub static l_term___u2229___00__closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2229___00__closed__1_value) as *mut LeanObject,
        (((70 as usize) << 1) | 1) as *mut LeanObject,
        (((70 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2229___00__closed__5_value) as *mut LeanObject,
    ],
};
static mut l_term___u2229___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2229___00__closed__6_value) as *mut LeanObject;
pub static mut l_term___u2229__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2229___00__closed__6_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2229____1___closed__0_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [73, 110, 116, 101, 114, 46, 105, 110, 116, 101, 114, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2229____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2229____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u2229____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___u2229____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u2229____1___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [73, 110, 116, 101, 114, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2229____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2229____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2229____1___closed__3_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 110, 116, 101, 114, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2229____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2229____1___closed__3_value)
        as *mut LeanObject;
static l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2229____1___closed__2_value
        ) as *mut LeanObject,
        9590123785770996304 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value:
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
            l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2229____1___closed__3_value
        ) as *mut LeanObject,
        8734591627461887881 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2229____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2229____1___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2229____1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2229____1___closed__5_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2229____1___closed__6_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2229____1___closed__5_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2229____1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2229____1___closed__6_value)
        as *mut LeanObject;
pub static l_term___x5c___00__closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 92, 95, 0],
};
static mut l_term___x5c___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___x5c___00__closed__0_value) as *mut LeanObject;
pub static l_term___x5c___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x5c___00__closed__0_value) as *mut LeanObject,
        4355727591741292209 as *mut LeanObject,
    ],
};
static mut l_term___x5c___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___x5c___00__closed__1_value) as *mut LeanObject;
pub static l_term___x5c___00__closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 92, 32, 0],
};
static mut l_term___x5c___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___x5c___00__closed__2_value) as *mut LeanObject;
pub static l_term___x5c___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___x5c___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___x5c___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___x5c___00__closed__3_value) as *mut LeanObject;
pub static l_term___x5c___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x5c___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2229___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x5c___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___x5c___00__closed__4_value) as *mut LeanObject;
pub static l_term___x5c___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x5c___00__closed__1_value) as *mut LeanObject,
        (((70 as usize) << 1) | 1) as *mut LeanObject,
        (((71 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x5c___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x5c___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___x5c___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___x5c__: *mut LeanObject =
    core::ptr::addr_of!(l_term___x5c___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x5c____1___closed__0_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [83, 68, 105, 102, 102, 46, 115, 100, 105, 102, 102, 0],
};
static mut l___aux__Init__Core______macroRules__term___x5c____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___x5c____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___x5c____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___x5c____1___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [83, 68, 105, 102, 102, 0],
};
static mut l___aux__Init__Core______macroRules__term___x5c____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x5c____1___closed__3_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 100, 105, 102, 102, 0],
};
static mut l___aux__Init__Core______macroRules__term___x5c____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__3_value)
        as *mut LeanObject;
static l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__2_value)
            as *mut LeanObject,
        13773288124037983708 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value: LeanCtorObject<
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
            l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__3_value)
            as *mut LeanObject,
        9260201674475043113 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x5c____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x5c____1___closed__5_value: LeanCtorObject<
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
        core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x5c____1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__5_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x5c____1___closed__6_value: LeanCtorObject<
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
        core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__5_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x5c____1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x5c____1___closed__6_value)
        as *mut LeanObject;
pub static l_term_x7b_x7d___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [116, 101, 114, 109, 123, 125, 0],
};
static mut l_term_x7b_x7d___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term_x7b_x7d___closed__0_value) as *mut LeanObject;
pub static l_term_x7b_x7d___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term_x7b_x7d___closed__0_value) as *mut LeanObject,
        5126085667538439468 as *mut LeanObject,
    ],
};
static mut l_term_x7b_x7d___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term_x7b_x7d___closed__1_value) as *mut LeanObject;
pub static l_term_x7b_x7d___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [123, 0],
};
static mut l_term_x7b_x7d___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term_x7b_x7d___closed__2_value) as *mut LeanObject;
pub static l_term_x7b_x7d___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term_x7b_x7d___closed__2_value) as *mut LeanObject],
};
static mut l_term_x7b_x7d___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term_x7b_x7d___closed__3_value) as *mut LeanObject;
pub static l_term_x7b_x7d___closed__4_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [125, 0],
};
static mut l_term_x7b_x7d___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term_x7b_x7d___closed__4_value) as *mut LeanObject;
pub static l_term_x7b_x7d___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term_x7b_x7d___closed__4_value) as *mut LeanObject],
};
static mut l_term_x7b_x7d___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term_x7b_x7d___closed__5_value) as *mut LeanObject;
pub static l_term_x7b_x7d___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x7b_x7d___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x7b_x7d___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_term_x7b_x7d___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term_x7b_x7d___closed__6_value) as *mut LeanObject;
pub static l_term_x7b_x7d___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_term_x7b_x7d___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term_x7b_x7d___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_term_x7b_x7d___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_term_x7b_x7d___closed__7_value) as *mut LeanObject;
pub static mut l_term_x7b_x7d: *mut LeanObject =
    core::ptr::addr_of!(l_term_x7b_x7d___closed__7_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0_value:
    LeanStringObject<32> = LeanStringObject {
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
        69, 109, 112, 116, 121, 67, 111, 108, 108, 101, 99, 116, 105, 111, 110, 46, 101, 109, 112,
        116, 121, 67, 111, 108, 108, 101, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__2_value:
    LeanStringObject<16> = LeanStringObject {
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
        69, 109, 112, 116, 121, 67, 111, 108, 108, 101, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__3_value:
    LeanStringObject<16> = LeanStringObject {
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
        101, 109, 112, 116, 121, 67, 111, 108, 108, 101, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__3_value)
        as *mut LeanObject;
static l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__2_value)
            as *mut LeanObject,
        14146683654382146028 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value: LeanCtorObject<
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
            l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__3_value)
            as *mut LeanObject,
        14960083141803914499 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__5_value: LeanCtorObject<
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
        core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__5_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6_value: LeanCtorObject<
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
        core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__5_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6_value)
        as *mut LeanObject;
pub static l_term_u2205___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 5,
    m_data: [116, 101, 114, 109, 226, 136, 133, 0],
};
static mut l_term_u2205___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term_u2205___closed__0_value) as *mut LeanObject;
pub static l_term_u2205___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term_u2205___closed__0_value) as *mut LeanObject,
        18206905930387346873 as *mut LeanObject,
    ],
};
static mut l_term_u2205___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term_u2205___closed__1_value) as *mut LeanObject;
pub static l_term_u2205___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 136, 133, 0],
};
static mut l_term_u2205___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term_u2205___closed__2_value) as *mut LeanObject;
pub static l_term_u2205___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term_u2205___closed__2_value) as *mut LeanObject],
};
static mut l_term_u2205___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term_u2205___closed__3_value) as *mut LeanObject;
pub static l_term_u2205___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_term_u2205___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term_u2205___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_term_u2205___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term_u2205___closed__4_value) as *mut LeanObject;
pub static mut l_term_u2205: *mut LeanObject =
    core::ptr::addr_of!(l_term_u2205___closed__4_value) as *mut LeanObject;
pub static mut l_Task_Priority_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Task_Priority_max: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Task_Priority_dedicated: *mut LeanObject = core::ptr::null_mut();
pub static l_term___x21_x3d___00__closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [116, 101, 114, 109, 95, 33, 61, 95, 0],
};
static mut l_term___x21_x3d___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___x21_x3d___00__closed__0_value) as *mut LeanObject;
pub static l_term___x21_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x21_x3d___00__closed__0_value) as *mut LeanObject,
        12618372790243287421 as *mut LeanObject,
    ],
};
static mut l_term___x21_x3d___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___x21_x3d___00__closed__1_value) as *mut LeanObject;
pub static l_term___x21_x3d___00__closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 33, 61, 32, 0],
};
static mut l_term___x21_x3d___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___x21_x3d___00__closed__2_value) as *mut LeanObject;
pub static l_term___x21_x3d___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___x21_x3d___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___x21_x3d___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___x21_x3d___00__closed__3_value) as *mut LeanObject;
pub static l_term___x21_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x21_x3d___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2248___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x21_x3d___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___x21_x3d___00__closed__4_value) as *mut LeanObject;
pub static l_term___x21_x3d___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x21_x3d___00__closed__1_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x21_x3d___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x21_x3d___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___x21_x3d___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___x21_x3d__: *mut LeanObject =
    core::ptr::addr_of!(l_term___x21_x3d___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0_value:
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
    m_data: [98, 110, 101, 0],
};
static mut l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0_value
        ) as *mut LeanObject,
        943799886658452456 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__3_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__3_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__0_value:
    LeanStringObject<15> = LeanStringObject {
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
        98, 105, 110, 114, 101, 108, 95, 110, 111, 95, 112, 114, 111, 112, 0,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__0_value)
        as *mut LeanObject;
static l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_0:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_1:
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
            l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_2:
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
            l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value:
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
            l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__0_value
        ) as *mut LeanObject,
        2715876919967644250 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2_value:
    LeanStringObject<16> = LeanStringObject {
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
        98, 105, 110, 114, 101, 108, 95, 110, 111, 95, 112, 114, 111, 112, 37, 0,
    ],
};
static mut l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2_value)
        as *mut LeanObject;
pub static l_term___u2260___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 137, 160, 95, 0],
};
static mut l_term___u2260___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2260___00__closed__0_value) as *mut LeanObject;
pub static l_term___u2260___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___u2260___00__closed__0_value) as *mut LeanObject,
        6870096354468370040 as *mut LeanObject,
    ],
};
static mut l_term___u2260___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2260___00__closed__1_value) as *mut LeanObject;
pub static l_term___u2260___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 137, 160, 32, 0],
};
static mut l_term___u2260___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2260___00__closed__2_value) as *mut LeanObject;
pub static l_term___u2260___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___u2260___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___u2260___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2260___00__closed__3_value) as *mut LeanObject;
pub static l_term___u2260___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x2d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2260___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2248___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2260___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2260___00__closed__4_value) as *mut LeanObject;
pub static l_term___u2260___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___u2260___00__closed__1_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___u2260___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___u2260___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2260___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___u2260__: *mut LeanObject =
    core::ptr::addr_of!(l_term___u2260___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2260____1___closed__0_value:
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
    m_data: [78, 101, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2260____1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2260____1___closed__0_value)
        as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___aux__Init__Core______macroRules__term___u2260____1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__term___u2260____1___closed__2_value:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2260____1___closed__0_value
        ) as *mut LeanObject,
        6695605208187598753 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2260____1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2260____1___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2260____1___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2260____1___closed__2_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2260____1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2260____1___closed__3_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2260____1___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2260____1___closed__3_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2260____1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2260____1___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2260____2___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [98, 105, 110, 114, 101, 108, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2260____2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2260____2___closed__0_value)
        as *mut LeanObject;
static l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_0:
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
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_1:
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
            l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_2:
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
            l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value
        ) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value:
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
            l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__Core______macroRules__term___u2260____2___closed__0_value
        ) as *mut LeanObject,
        11955267307951615569 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Core______macroRules__term___u2260____2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__term___u2260____2___closed__2_value:
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
    m_data: [98, 105, 110, 114, 101, 108, 37, 0],
};
static mut l___aux__Init__Core______macroRules__term___u2260____2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___u2260____2___closed__2_value)
        as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0]};
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__1_value
) as *mut LeanObject;
static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__1_value) as *mut LeanObject,3294379458557754569 as *mut LeanObject] };
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3_value
) as *mut LeanObject;
static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3_value) as *mut LeanObject,14997215300048349804 as *mut LeanObject] };
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 102, 102, 46, 114, 102, 108, 0]};
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5_value
) as *mut LeanObject;
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 102, 108, 0]};
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__7_value
) as *mut LeanObject;
static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5_value) as *mut LeanObject,9917798623386220051 as *mut LeanObject] };
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__7_value) as *mut LeanObject,3546295369065387461 as *mut LeanObject] };
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__9_value
) as *mut LeanObject;
pub static l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10_value
) as *mut LeanObject;
pub static mut l_instTransIff: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instDecidableTrue: u8 = 0;
pub static mut l_instDecidableFalse: u8 = 0;
pub static l_noConfusionEnum___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_noConfusionEnum___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_noConfusionEnum___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_noConfusionEnum___redArg___closed__0_value) as *mut LeanObject;
pub static mut l_instInhabitedProp: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedNonScalar_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedNonScalar: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedPNonScalar_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedPNonScalar: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedTrue: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedPUnit: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_instBEqOption_beq___redArg(
    mut v_inst_3128_: *mut LeanObject,
    mut v_x_3129_: *mut LeanObject,
    mut v_x_3130_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3129_) == 0 {
        lean_dec_ref(v_inst_3128_);
        if lean_obj_tag(v_x_3130_) == 0 {
            let mut v___x_3131_: u8 = 0;
            v___x_3131_ = 1;
            return v___x_3131_;
        } else {
            let mut v___x_3132_: u8 = 0;
            lean_dec_ref_known(v_x_3130_, 1);
            v___x_3132_ = 0;
            return v___x_3132_;
        }
    } else {
        if lean_obj_tag(v_x_3130_) == 0 {
            let mut v___x_3133_: u8 = 0;
            lean_dec_ref_known(v_x_3129_, 1);
            lean_dec_ref(v_inst_3128_);
            v___x_3133_ = 0;
            return v___x_3133_;
        } else {
            let mut v_val_3134_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_3135_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3137_: u8 = 0;
            v_val_3134_ = lean_ctor_get(v_x_3129_, 0);
            lean_inc(v_val_3134_);
            lean_dec_ref_known(v_x_3129_, 1);
            v_val_3135_ = lean_ctor_get(v_x_3130_, 0);
            lean_inc(v_val_3135_);
            lean_dec_ref_known(v_x_3130_, 1);
            v___x_3136_ = lean_apply_2(v_inst_3128_, v_val_3134_, v_val_3135_);
            v___x_3137_ = (lean_unbox(v___x_3136_) as u8);
            return v___x_3137_;
        }
    }
}
pub unsafe fn l_instBEqOption_beq___redArg___boxed(
    mut v_inst_3138_: *mut LeanObject,
    mut v_x_3139_: *mut LeanObject,
    mut v_x_3140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3141_: u8 = 0;
    let mut v_r_3142_: *mut LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_instBEqOption_beq___redArg(v_inst_3138_, v_x_3139_, v_x_3140_);
    v_r_3142_ = lean_box((v_res_3141_) as usize);
    return v_r_3142_;
}
pub unsafe fn l_instBEqOption_beq(
    mut v_00_u03b1_3143_: *mut LeanObject,
    mut v_inst_3144_: *mut LeanObject,
    mut v_x_3145_: *mut LeanObject,
    mut v_x_3146_: *mut LeanObject,
) -> u8 {
    let mut v___x_3147_: u8 = 0;
    v___x_3147_ = l_instBEqOption_beq___redArg(v_inst_3144_, v_x_3145_, v_x_3146_);
    return v___x_3147_;
}
pub unsafe fn l_instBEqOption_beq___boxed(
    mut v_00_u03b1_3148_: *mut LeanObject,
    mut v_inst_3149_: *mut LeanObject,
    mut v_x_3150_: *mut LeanObject,
    mut v_x_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3152_: u8 = 0;
    let mut v_r_3153_: *mut LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_instBEqOption_beq(v_00_u03b1_3148_, v_inst_3149_, v_x_3150_, v_x_3151_);
    v_r_3153_ = lean_box((v_res_3152_) as usize);
    return v_r_3153_;
}
pub unsafe fn l_instBEqOption___redArg(mut v_inst_3154_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    v___x_3155_ = lean_alloc_closure(l_instBEqOption_beq___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3155_, 0, lean_box(0));
    lean_closure_set(v___x_3155_, 1, v_inst_3154_);
    return v___x_3155_;
}
pub unsafe fn l_instBEqOption(
    mut v_00_u03b1_3156_: *mut LeanObject,
    mut v_inst_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    v___x_3158_ = lean_alloc_closure(l_instBEqOption_beq___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_3158_, 0, lean_box(0));
    lean_closure_set(v___x_3158_, 1, v_inst_3157_);
    return v___x_3158_;
}
pub unsafe fn l_inline___redArg(mut v_a_3159_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_3159_);
    return v_a_3159_;
}
pub unsafe fn l_inline___redArg___boxed(mut v_a_3160_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3161_: *mut LeanObject = core::ptr::null_mut();
    v_res_3161_ = l_inline___redArg(v_a_3160_);
    lean_dec(v_a_3160_);
    return v_res_3161_;
}
pub unsafe fn l_inline(
    mut v_00_u03b1_3162_: *mut LeanObject,
    mut v_a_3163_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_3163_);
    return v_a_3163_;
}
pub unsafe fn l_inline___boxed(
    mut v_00_u03b1_3164_: *mut LeanObject,
    mut v_a_3165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3166_: *mut LeanObject = core::ptr::null_mut();
    v_res_3166_ = l_inline(v_00_u03b1_3164_, v_a_3165_);
    lean_dec(v_a_3165_);
    return v_res_3166_;
}
pub unsafe fn l_eagerReduce___redArg(mut v_a_3167_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_3167_);
    return v_a_3167_;
}
pub unsafe fn l_eagerReduce___redArg___boxed(mut v_a_3168_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3169_: *mut LeanObject = core::ptr::null_mut();
    v_res_3169_ = l_eagerReduce___redArg(v_a_3168_);
    lean_dec(v_a_3168_);
    return v_res_3169_;
}
pub unsafe fn l_eagerReduce(
    mut v_00_u03b1_3170_: *mut LeanObject,
    mut v_a_3171_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_3171_);
    return v_a_3171_;
}
pub unsafe fn l_eagerReduce___boxed(
    mut v_00_u03b1_3172_: *mut LeanObject,
    mut v_a_3173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3174_: *mut LeanObject = core::ptr::null_mut();
    v_res_3174_ = l_eagerReduce(v_00_u03b1_3172_, v_a_3173_);
    lean_dec(v_a_3173_);
    return v_res_3174_;
}
pub unsafe fn l_flip___redArg(
    mut v_f_3175_: *mut LeanObject,
    mut v_b_3176_: *mut LeanObject,
    mut v_a_3177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    v___x_3178_ = lean_apply_2(v_f_3175_, v_a_3177_, v_b_3176_);
    return v___x_3178_;
}
pub unsafe fn l_flip(
    mut v_00_u03b1_3179_: *mut LeanObject,
    mut v_00_u03b2_3180_: *mut LeanObject,
    mut v_00_u03c6_3181_: *mut LeanObject,
    mut v_f_3182_: *mut LeanObject,
    mut v_b_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    v___x_3185_ = lean_apply_2(v_f_3182_, v_a_3184_, v_b_3183_);
    return v___x_3185_;
}
pub unsafe fn l_instDecidableEqEmpty(mut v_a_3186_: u8, mut v_b_3187_: u8) -> u8 {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_instDecidableEqEmpty___boxed(
    mut v_a_3188_: *mut LeanObject,
    mut v_b_3189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3190_: u8 = 0;
    let mut v_b_boxed_3191_: u8 = 0;
    let mut v_res_3192_: u8 = 0;
    let mut v_r_3193_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3190_ = (lean_unbox(v_a_3188_) as u8);
    v_b_boxed_3191_ = (lean_unbox(v_b_3189_) as u8);
    v_res_3192_ = l_instDecidableEqEmpty(v_a_boxed_3190_, v_b_boxed_3191_);
    v_r_3193_ = lean_box((v_res_3192_) as usize);
    return v_r_3193_;
}
pub unsafe fn l_instDecidableEqPEmpty(mut v_a_3194_: u8, mut v_b_3195_: u8) -> u8 {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_instDecidableEqPEmpty___boxed(
    mut v_a_3196_: *mut LeanObject,
    mut v_b_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3198_: u8 = 0;
    let mut v_b_boxed_3199_: u8 = 0;
    let mut v_res_3200_: u8 = 0;
    let mut v_r_3201_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3198_ = (lean_unbox(v_a_3196_) as u8);
    v_b_boxed_3199_ = (lean_unbox(v_b_3197_) as u8);
    v_res_3200_ = l_instDecidableEqPEmpty(v_a_boxed_3198_, v_b_boxed_3199_);
    v_r_3201_ = lean_box((v_res_3200_) as usize);
    return v_r_3201_;
}
pub unsafe fn l_Thunk_mk___boxed(
    mut v_00_u03b1_3204_: *mut LeanObject,
    mut v_fn_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3206_: *mut LeanObject = core::ptr::null_mut();
    v_res_3206_ = lean_mk_thunk(v_fn_3205_);
    return v_res_3206_;
}
pub unsafe fn l_Thunk_pure___boxed(
    mut v_00_u03b1_3209_: *mut LeanObject,
    mut v_a_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3211_: *mut LeanObject = core::ptr::null_mut();
    v_res_3211_ = lean_thunk_pure(v_a_3210_);
    return v_res_3211_;
}
pub unsafe fn l_Thunk_get___boxed(
    mut v_00_u03b1_3214_: *mut LeanObject,
    mut v_x_3215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3216_: *mut LeanObject = core::ptr::null_mut();
    v_res_3216_ = lean_thunk_get_own(v_x_3215_);
    lean_dec_ref(v_x_3215_);
    return v_res_3216_;
}
pub unsafe fn l_Thunk_fnImpl___redArg(mut v_x_3217_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    v___x_3218_ = lean_thunk_get_own(v_x_3217_);
    return v___x_3218_;
}
pub unsafe fn l_Thunk_fnImpl___redArg___boxed(mut v_x_3219_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3220_: *mut LeanObject = core::ptr::null_mut();
    v_res_3220_ = l_Thunk_fnImpl___redArg(v_x_3219_);
    lean_dec_ref(v_x_3219_);
    return v_res_3220_;
}
pub unsafe fn l_Thunk_fnImpl(
    mut v_00_u03b1_3221_: *mut LeanObject,
    mut v_x_3222_: *mut LeanObject,
    mut v_x_3223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    v___x_3224_ = lean_thunk_get_own(v_x_3222_);
    return v___x_3224_;
}
pub unsafe fn l_Thunk_fnImpl___boxed(
    mut v_00_u03b1_3225_: *mut LeanObject,
    mut v_x_3226_: *mut LeanObject,
    mut v_x_3227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3228_: *mut LeanObject = core::ptr::null_mut();
    v_res_3228_ = l_Thunk_fnImpl(v_00_u03b1_3225_, v_x_3226_, v_x_3227_);
    lean_dec_ref(v_x_3226_);
    return v_res_3228_;
}
pub unsafe fn l_Thunk_map___redArg___lam__0(
    mut v_x_3229_: *mut LeanObject,
    mut v_f_3230_: *mut LeanObject,
    mut v_x_3231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    v___x_3232_ = lean_thunk_get_own(v_x_3229_);
    v___x_3233_ = lean_apply_1(v_f_3230_, v___x_3232_);
    return v___x_3233_;
}
pub unsafe fn l_Thunk_map___redArg___lam__0___boxed(
    mut v_x_3234_: *mut LeanObject,
    mut v_f_3235_: *mut LeanObject,
    mut v_x_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3237_: *mut LeanObject = core::ptr::null_mut();
    v_res_3237_ = l_Thunk_map___redArg___lam__0(v_x_3234_, v_f_3235_, v_x_3236_);
    lean_dec_ref(v_x_3234_);
    return v_res_3237_;
}
pub unsafe fn l_Thunk_map___redArg(
    mut v_f_3238_: *mut LeanObject,
    mut v_x_3239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    v___f_3240_ = lean_alloc_closure(
        l_Thunk_map___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3240_, 0, v_x_3239_);
    lean_closure_set(v___f_3240_, 1, v_f_3238_);
    v___x_3241_ = lean_mk_thunk(v___f_3240_);
    return v___x_3241_;
}
pub unsafe fn l_Thunk_map(
    mut v_00_u03b1_3242_: *mut LeanObject,
    mut v_00_u03b2_3243_: *mut LeanObject,
    mut v_f_3244_: *mut LeanObject,
    mut v_x_3245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    v___f_3246_ = lean_alloc_closure(
        l_Thunk_map___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3246_, 0, v_x_3245_);
    lean_closure_set(v___f_3246_, 1, v_f_3244_);
    v___x_3247_ = lean_mk_thunk(v___f_3246_);
    return v___x_3247_;
}
pub unsafe fn l_Thunk_bind___redArg___lam__0(
    mut v_x_3248_: *mut LeanObject,
    mut v_f_3249_: *mut LeanObject,
    mut v_x_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    v___x_3251_ = lean_thunk_get_own(v_x_3248_);
    v___x_3252_ = lean_apply_1(v_f_3249_, v___x_3251_);
    v___x_3253_ = lean_thunk_get_own(v___x_3252_);
    lean_dec_ref(v___x_3252_);
    return v___x_3253_;
}
pub unsafe fn l_Thunk_bind___redArg___lam__0___boxed(
    mut v_x_3254_: *mut LeanObject,
    mut v_f_3255_: *mut LeanObject,
    mut v_x_3256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3257_: *mut LeanObject = core::ptr::null_mut();
    v_res_3257_ = l_Thunk_bind___redArg___lam__0(v_x_3254_, v_f_3255_, v_x_3256_);
    lean_dec_ref(v_x_3254_);
    return v_res_3257_;
}
pub unsafe fn l_Thunk_bind___redArg(
    mut v_x_3258_: *mut LeanObject,
    mut v_f_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    v___f_3260_ = lean_alloc_closure(
        l_Thunk_bind___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3260_, 0, v_x_3258_);
    lean_closure_set(v___f_3260_, 1, v_f_3259_);
    v___x_3261_ = lean_mk_thunk(v___f_3260_);
    return v___x_3261_;
}
pub unsafe fn l_Thunk_bind(
    mut v_00_u03b1_3262_: *mut LeanObject,
    mut v_00_u03b2_3263_: *mut LeanObject,
    mut v_x_3264_: *mut LeanObject,
    mut v_f_3265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    v___f_3266_ = lean_alloc_closure(
        l_Thunk_bind___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3266_, 0, v_x_3264_);
    lean_closure_set(v___f_3266_, 1, v_f_3265_);
    v___x_3267_ = lean_mk_thunk(v___f_3266_);
    return v___x_3267_;
}
pub unsafe fn l_thunkCoe___lam__0(
    mut v_a_3268_: *mut LeanObject,
    mut v_x_3269_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_3268_);
    return v_a_3268_;
}
pub unsafe fn l_thunkCoe___lam__0___boxed(
    mut v_a_3270_: *mut LeanObject,
    mut v_x_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3272_: *mut LeanObject = core::ptr::null_mut();
    v_res_3272_ = l_thunkCoe___lam__0(v_a_3270_, v_x_3271_);
    lean_dec(v_a_3270_);
    return v_res_3272_;
}
pub unsafe fn l_thunkCoe___lam__1(mut v_a_3273_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    v___f_3274_ = lean_alloc_closure(l_thunkCoe___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_3274_, 0, v_a_3273_);
    v___x_3275_ = lean_mk_thunk(v___f_3274_);
    return v___x_3275_;
}
pub unsafe fn l_thunkCoe(mut v_00_u03b1_3277_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_3278_: *mut LeanObject = core::ptr::null_mut();
    v___f_3278_ = l_thunkCoe___closed__0;
    return v___f_3278_;
}
pub unsafe fn l_instInhabitedThunk___redArg(mut v_inst_3279_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    v___x_3280_ = lean_thunk_pure(v_inst_3279_);
    return v___x_3280_;
}
pub unsafe fn l_instInhabitedThunk(
    mut v_00_u03b1_3281_: *mut LeanObject,
    mut v_inst_3282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    v___x_3283_ = lean_thunk_pure(v_inst_3282_);
    return v___x_3283_;
}
pub unsafe fn l_Eq_ndrecOn___redArg(mut v_m_3284_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_m_3284_);
    return v_m_3284_;
}
pub unsafe fn l_Eq_ndrecOn___redArg___boxed(mut v_m_3285_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3286_: *mut LeanObject = core::ptr::null_mut();
    v_res_3286_ = l_Eq_ndrecOn___redArg(v_m_3285_);
    lean_dec(v_m_3285_);
    return v_res_3286_;
}
pub unsafe fn l_Eq_ndrecOn(
    mut v_00_u03b1_3287_: *mut LeanObject,
    mut v_a_3288_: *mut LeanObject,
    mut v_motive_3289_: *mut LeanObject,
    mut v_b_3290_: *mut LeanObject,
    mut v_h_3291_: *mut LeanObject,
    mut v_m_3292_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_m_3292_);
    return v_m_3292_;
}
pub unsafe fn l_Eq_ndrecOn___boxed(
    mut v_00_u03b1_3293_: *mut LeanObject,
    mut v_a_3294_: *mut LeanObject,
    mut v_motive_3295_: *mut LeanObject,
    mut v_b_3296_: *mut LeanObject,
    mut v_h_3297_: *mut LeanObject,
    mut v_m_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3299_: *mut LeanObject = core::ptr::null_mut();
    v_res_3299_ = l_Eq_ndrecOn(
        v_00_u03b1_3293_,
        v_a_3294_,
        v_motive_3295_,
        v_b_3296_,
        v_h_3297_,
        v_m_3298_,
    );
    lean_dec(v_m_3298_);
    lean_dec(v_b_3296_);
    lean_dec(v_a_3294_);
    return v_res_3299_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6()
-> *mut LeanObject {
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    v___x_3335_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5;
    v___x_3336_ = l_String_toRawSubstring_x27(v___x_3335_);
    return v___x_3336_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1(
    mut v_x_3353_: *mut LeanObject,
    mut v_a_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: u8 = 0;
    v___x_3356_ = l_term___x3c_x2d_x3e___00__closed__1;
    lean_inc(v_x_3353_);
    v___x_3357_ = l_Lean_Syntax_isOfKind(v_x_3353_, v___x_3356_);
    if v___x_3357_ == 0 {
        let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3353_);
        v___x_3358_ = lean_box(1);
        v___x_3359_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3359_, 0, v___x_3358_);
        lean_ctor_set(v___x_3359_, 1, v_a_3355_);
        return v___x_3359_;
    } else {
        let mut v_quotContext_3360_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3361_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3367_: u8 = 0;
        let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_3360_ = lean_ctor_get(v_a_3354_, 1);
        v_currMacroScope_3361_ = lean_ctor_get(v_a_3354_, 2);
        v_ref_3362_ = lean_ctor_get(v_a_3354_, 5);
        v___x_3363_ = lean_unsigned_to_nat(0);
        v___x_3364_ = l_Lean_Syntax_getArg(v_x_3353_, v___x_3363_);
        v___x_3365_ = lean_unsigned_to_nat(2);
        v___x_3366_ = l_Lean_Syntax_getArg(v_x_3353_, v___x_3365_);
        lean_dec(v_x_3353_);
        v___x_3367_ = 0;
        v___x_3368_ = l_Lean_SourceInfo_fromRef(v_ref_3362_, v___x_3367_);
        v___x_3369_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_3370_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once
            ),
            _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6,
        );
        v___x_3371_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7;
        lean_inc(v_currMacroScope_3361_);
        lean_inc(v_quotContext_3360_);
        v___x_3372_ =
            l_Lean_addMacroScope(v_quotContext_3360_, v___x_3371_, v_currMacroScope_3361_);
        v___x_3373_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11;
        lean_inc_n(v___x_3368_, 2);
        v___x_3374_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3374_, 0, v___x_3368_);
        lean_ctor_set(v___x_3374_, 1, v___x_3370_);
        lean_ctor_set(v___x_3374_, 2, v___x_3372_);
        lean_ctor_set(v___x_3374_, 3, v___x_3373_);
        v___x_3375_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_3376_ = l_Lean_Syntax_node2(v___x_3368_, v___x_3375_, v___x_3364_, v___x_3366_);
        v___x_3377_ = l_Lean_Syntax_node2(v___x_3368_, v___x_3369_, v___x_3374_, v___x_3376_);
        v___x_3378_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3378_, 0, v___x_3377_);
        lean_ctor_set(v___x_3378_, 1, v_a_3355_);
        return v___x_3378_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___boxed(
    mut v_x_3379_: *mut LeanObject,
    mut v_a_3380_: *mut LeanObject,
    mut v_a_3381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3382_: *mut LeanObject = core::ptr::null_mut();
    v_res_3382_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1(
        v_x_3379_, v_a_3380_, v_a_3381_,
    );
    lean_dec_ref(v_a_3380_);
    return v_res_3382_;
}
pub unsafe fn l___aux__Init__Core______unexpand__Iff__1(
    mut v_x_3386_: *mut LeanObject,
    mut v_a_3387_: *mut LeanObject,
    mut v_a_3388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: u8 = 0;
    v___x_3389_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_3386_);
    v___x_3390_ = l_Lean_Syntax_isOfKind(v_x_3386_, v___x_3389_);
    if v___x_3390_ == 0 {
        let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3386_);
        v___x_3391_ = lean_box(0);
        v___x_3392_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3392_, 0, v___x_3391_);
        lean_ctor_set(v___x_3392_, 1, v_a_3388_);
        return v___x_3392_;
    } else {
        let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3396_: u8 = 0;
        v___x_3393_ = lean_unsigned_to_nat(0);
        v___x_3394_ = l_Lean_Syntax_getArg(v_x_3386_, v___x_3393_);
        v___x_3395_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_3394_);
        v___x_3396_ = l_Lean_Syntax_isOfKind(v___x_3394_, v___x_3395_);
        if v___x_3396_ == 0 {
            let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_3394_);
            lean_dec(v_x_3386_);
            v___x_3397_ = lean_box(0);
            v___x_3398_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_3398_, 0, v___x_3397_);
            lean_ctor_set(v___x_3398_, 1, v_a_3388_);
            return v___x_3398_;
        } else {
            let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3402_: u8 = 0;
            v___x_3399_ = lean_unsigned_to_nat(1);
            v___x_3400_ = l_Lean_Syntax_getArg(v_x_3386_, v___x_3399_);
            lean_dec(v_x_3386_);
            v___x_3401_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_3400_);
            v___x_3402_ = l_Lean_Syntax_matchesNull(v___x_3400_, v___x_3401_);
            if v___x_3402_ == 0 {
                let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_3400_);
                lean_dec(v___x_3394_);
                v___x_3403_ = lean_box(0);
                v___x_3404_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3404_, 0, v___x_3403_);
                lean_ctor_set(v___x_3404_, 1, v_a_3388_);
                return v___x_3404_;
            } else {
                let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_3407_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3408_: u8 = 0;
                let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
                v___x_3405_ = l_Lean_Syntax_getArg(v___x_3400_, v___x_3393_);
                v___x_3406_ = l_Lean_Syntax_getArg(v___x_3400_, v___x_3399_);
                lean_dec(v___x_3400_);
                v_ref_3407_ = l_Lean_replaceRef(v___x_3394_, v_a_3387_);
                lean_dec(v___x_3394_);
                v___x_3408_ = 0;
                v___x_3409_ = l_Lean_SourceInfo_fromRef(v_ref_3407_, v___x_3408_);
                lean_dec(v_ref_3407_);
                v___x_3410_ = l_term___x3c_x2d_x3e___00__closed__1;
                v___x_3411_ = l_term___x3c_x2d_x3e___00__closed__4;
                lean_inc(v___x_3409_);
                v___x_3412_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3412_, 0, v___x_3409_);
                lean_ctor_set(v___x_3412_, 1, v___x_3411_);
                v___x_3413_ = l_Lean_Syntax_node3(
                    v___x_3409_,
                    v___x_3410_,
                    v___x_3405_,
                    v___x_3412_,
                    v___x_3406_,
                );
                v___x_3414_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3414_, 0, v___x_3413_);
                lean_ctor_set(v___x_3414_, 1, v_a_3388_);
                return v___x_3414_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__Iff__1___boxed(
    mut v_x_3415_: *mut LeanObject,
    mut v_a_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3418_: *mut LeanObject = core::ptr::null_mut();
    v_res_3418_ = l___aux__Init__Core______unexpand__Iff__1(v_x_3415_, v_a_3416_, v_a_3417_);
    lean_dec(v_a_3416_);
    return v_res_3418_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2194____1(
    mut v_x_3435_: *mut LeanObject,
    mut v_a_3436_: *mut LeanObject,
    mut v_a_3437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: u8 = 0;
    v___x_3438_ = l_term___u2194___00__closed__1;
    lean_inc(v_x_3435_);
    v___x_3439_ = l_Lean_Syntax_isOfKind(v_x_3435_, v___x_3438_);
    if v___x_3439_ == 0 {
        let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3435_);
        v___x_3440_ = lean_box(1);
        v___x_3441_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3441_, 0, v___x_3440_);
        lean_ctor_set(v___x_3441_, 1, v_a_3437_);
        return v___x_3441_;
    } else {
        let mut v_quotContext_3442_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3443_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3449_: u8 = 0;
        let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_3442_ = lean_ctor_get(v_a_3436_, 1);
        v_currMacroScope_3443_ = lean_ctor_get(v_a_3436_, 2);
        v_ref_3444_ = lean_ctor_get(v_a_3436_, 5);
        v___x_3445_ = lean_unsigned_to_nat(0);
        v___x_3446_ = l_Lean_Syntax_getArg(v_x_3435_, v___x_3445_);
        v___x_3447_ = lean_unsigned_to_nat(2);
        v___x_3448_ = l_Lean_Syntax_getArg(v_x_3435_, v___x_3447_);
        lean_dec(v_x_3435_);
        v___x_3449_ = 0;
        v___x_3450_ = l_Lean_SourceInfo_fromRef(v_ref_3444_, v___x_3449_);
        v___x_3451_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_3452_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once
            ),
            _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6,
        );
        v___x_3453_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7;
        lean_inc(v_currMacroScope_3443_);
        lean_inc(v_quotContext_3442_);
        v___x_3454_ =
            l_Lean_addMacroScope(v_quotContext_3442_, v___x_3453_, v_currMacroScope_3443_);
        v___x_3455_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11;
        lean_inc_n(v___x_3450_, 2);
        v___x_3456_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3456_, 0, v___x_3450_);
        lean_ctor_set(v___x_3456_, 1, v___x_3452_);
        lean_ctor_set(v___x_3456_, 2, v___x_3454_);
        lean_ctor_set(v___x_3456_, 3, v___x_3455_);
        v___x_3457_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_3458_ = l_Lean_Syntax_node2(v___x_3450_, v___x_3457_, v___x_3446_, v___x_3448_);
        v___x_3459_ = l_Lean_Syntax_node2(v___x_3450_, v___x_3451_, v___x_3456_, v___x_3458_);
        v___x_3460_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3460_, 0, v___x_3459_);
        lean_ctor_set(v___x_3460_, 1, v_a_3437_);
        return v___x_3460_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2194____1___boxed(
    mut v_x_3461_: *mut LeanObject,
    mut v_a_3462_: *mut LeanObject,
    mut v_a_3463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3464_: *mut LeanObject = core::ptr::null_mut();
    v_res_3464_ =
        l___aux__Init__Core______macroRules__term___u2194____1(v_x_3461_, v_a_3462_, v_a_3463_);
    lean_dec_ref(v_a_3462_);
    return v_res_3464_;
}
pub unsafe fn l___aux__Init__Core______unexpand__Iff__2(
    mut v_x_3465_: *mut LeanObject,
    mut v_a_3466_: *mut LeanObject,
    mut v_a_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u8 = 0;
    v___x_3468_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_3465_);
    v___x_3469_ = l_Lean_Syntax_isOfKind(v_x_3465_, v___x_3468_);
    if v___x_3469_ == 0 {
        let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3465_);
        v___x_3470_ = lean_box(0);
        v___x_3471_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3471_, 0, v___x_3470_);
        lean_ctor_set(v___x_3471_, 1, v_a_3467_);
        return v___x_3471_;
    } else {
        let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3475_: u8 = 0;
        v___x_3472_ = lean_unsigned_to_nat(0);
        v___x_3473_ = l_Lean_Syntax_getArg(v_x_3465_, v___x_3472_);
        v___x_3474_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_3473_);
        v___x_3475_ = l_Lean_Syntax_isOfKind(v___x_3473_, v___x_3474_);
        if v___x_3475_ == 0 {
            let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_3473_);
            lean_dec(v_x_3465_);
            v___x_3476_ = lean_box(0);
            v___x_3477_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_3477_, 0, v___x_3476_);
            lean_ctor_set(v___x_3477_, 1, v_a_3467_);
            return v___x_3477_;
        } else {
            let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3481_: u8 = 0;
            v___x_3478_ = lean_unsigned_to_nat(1);
            v___x_3479_ = l_Lean_Syntax_getArg(v_x_3465_, v___x_3478_);
            lean_dec(v_x_3465_);
            v___x_3480_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_3479_);
            v___x_3481_ = l_Lean_Syntax_matchesNull(v___x_3479_, v___x_3480_);
            if v___x_3481_ == 0 {
                let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_3479_);
                lean_dec(v___x_3473_);
                v___x_3482_ = lean_box(0);
                v___x_3483_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3483_, 0, v___x_3482_);
                lean_ctor_set(v___x_3483_, 1, v_a_3467_);
                return v___x_3483_;
            } else {
                let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_3486_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3487_: u8 = 0;
                let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
                v___x_3484_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_3472_);
                v___x_3485_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_3478_);
                lean_dec(v___x_3479_);
                v_ref_3486_ = l_Lean_replaceRef(v___x_3473_, v_a_3466_);
                lean_dec(v___x_3473_);
                v___x_3487_ = 0;
                v___x_3488_ = l_Lean_SourceInfo_fromRef(v_ref_3486_, v___x_3487_);
                lean_dec(v_ref_3486_);
                v___x_3489_ = l_term___u2194___00__closed__1;
                v___x_3490_ = l_term___u2194___00__closed__2;
                lean_inc(v___x_3488_);
                v___x_3491_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3491_, 0, v___x_3488_);
                lean_ctor_set(v___x_3491_, 1, v___x_3490_);
                v___x_3492_ = l_Lean_Syntax_node3(
                    v___x_3488_,
                    v___x_3489_,
                    v___x_3484_,
                    v___x_3491_,
                    v___x_3485_,
                );
                v___x_3493_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3493_, 0, v___x_3492_);
                lean_ctor_set(v___x_3493_, 1, v_a_3467_);
                return v___x_3493_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__Iff__2___boxed(
    mut v_x_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3497_: *mut LeanObject = core::ptr::null_mut();
    v_res_3497_ = l___aux__Init__Core______unexpand__Iff__2(v_x_3494_, v_a_3495_, v_a_3496_);
    lean_dec(v_a_3495_);
    return v_res_3497_;
}
pub unsafe fn l_Sum_ctorIdx___redArg(mut v_x_3498_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_3498_) == 0 {
        let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
        v___x_3499_ = lean_unsigned_to_nat(0);
        return v___x_3499_;
    } else {
        let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
        v___x_3500_ = lean_unsigned_to_nat(1);
        return v___x_3500_;
    }
}
pub unsafe fn l_Sum_ctorIdx___redArg___boxed(mut v_x_3501_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3502_: *mut LeanObject = core::ptr::null_mut();
    v_res_3502_ = l_Sum_ctorIdx___redArg(v_x_3501_);
    lean_dec_ref(v_x_3501_);
    return v_res_3502_;
}
pub unsafe fn l_Sum_ctorIdx(
    mut v_00_u03b1_3503_: *mut LeanObject,
    mut v_00_u03b2_3504_: *mut LeanObject,
    mut v_x_3505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    v___x_3506_ = l_Sum_ctorIdx___redArg(v_x_3505_);
    return v___x_3506_;
}
pub unsafe fn l_Sum_ctorIdx___boxed(
    mut v_00_u03b1_3507_: *mut LeanObject,
    mut v_00_u03b2_3508_: *mut LeanObject,
    mut v_x_3509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3510_: *mut LeanObject = core::ptr::null_mut();
    v_res_3510_ = l_Sum_ctorIdx(v_00_u03b1_3507_, v_00_u03b2_3508_, v_x_3509_);
    lean_dec_ref(v_x_3509_);
    return v_res_3510_;
}
pub unsafe fn l_Sum_ctorElim___redArg(
    mut v_t_3511_: *mut LeanObject,
    mut v_k_3512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    v_val_3513_ = lean_ctor_get(v_t_3511_, 0);
    lean_inc(v_val_3513_);
    lean_dec_ref(v_t_3511_);
    v___x_3514_ = lean_apply_1(v_k_3512_, v_val_3513_);
    return v___x_3514_;
}
pub unsafe fn l_Sum_ctorElim(
    mut v_00_u03b1_3515_: *mut LeanObject,
    mut v_00_u03b2_3516_: *mut LeanObject,
    mut v_motive_3517_: *mut LeanObject,
    mut v_ctorIdx_3518_: *mut LeanObject,
    mut v_t_3519_: *mut LeanObject,
    mut v_h_3520_: *mut LeanObject,
    mut v_k_3521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    v___x_3522_ = l_Sum_ctorElim___redArg(v_t_3519_, v_k_3521_);
    return v___x_3522_;
}
pub unsafe fn l_Sum_ctorElim___boxed(
    mut v_00_u03b1_3523_: *mut LeanObject,
    mut v_00_u03b2_3524_: *mut LeanObject,
    mut v_motive_3525_: *mut LeanObject,
    mut v_ctorIdx_3526_: *mut LeanObject,
    mut v_t_3527_: *mut LeanObject,
    mut v_h_3528_: *mut LeanObject,
    mut v_k_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3530_: *mut LeanObject = core::ptr::null_mut();
    v_res_3530_ = l_Sum_ctorElim(
        v_00_u03b1_3523_,
        v_00_u03b2_3524_,
        v_motive_3525_,
        v_ctorIdx_3526_,
        v_t_3527_,
        v_h_3528_,
        v_k_3529_,
    );
    lean_dec(v_ctorIdx_3526_);
    return v_res_3530_;
}
pub unsafe fn l_Sum_inl_elim___redArg(
    mut v_t_3531_: *mut LeanObject,
    mut v_inl_3532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    v___x_3533_ = l_Sum_ctorElim___redArg(v_t_3531_, v_inl_3532_);
    return v___x_3533_;
}
pub unsafe fn l_Sum_inl_elim(
    mut v_00_u03b1_3534_: *mut LeanObject,
    mut v_00_u03b2_3535_: *mut LeanObject,
    mut v_motive_3536_: *mut LeanObject,
    mut v_t_3537_: *mut LeanObject,
    mut v_h_3538_: *mut LeanObject,
    mut v_inl_3539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    v___x_3540_ = l_Sum_ctorElim___redArg(v_t_3537_, v_inl_3539_);
    return v___x_3540_;
}
pub unsafe fn l_Sum_inr_elim___redArg(
    mut v_t_3541_: *mut LeanObject,
    mut v_inr_3542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    v___x_3543_ = l_Sum_ctorElim___redArg(v_t_3541_, v_inr_3542_);
    return v___x_3543_;
}
pub unsafe fn l_Sum_inr_elim(
    mut v_00_u03b1_3544_: *mut LeanObject,
    mut v_00_u03b2_3545_: *mut LeanObject,
    mut v_motive_3546_: *mut LeanObject,
    mut v_t_3547_: *mut LeanObject,
    mut v_h_3548_: *mut LeanObject,
    mut v_inr_3549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    v___x_3550_ = l_Sum_ctorElim___redArg(v_t_3547_, v_inr_3549_);
    return v___x_3550_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1()
-> *mut LeanObject {
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    v___x_3571_ = l___aux__Init__Core______macroRules__term___u2295____1___closed__0;
    v___x_3572_ = l_String_toRawSubstring_x27(v___x_3571_);
    return v___x_3572_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2295____1(
    mut v_x_3586_: *mut LeanObject,
    mut v_a_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u8 = 0;
    v___x_3589_ = l_term___u2295___00__closed__1;
    lean_inc(v_x_3586_);
    v___x_3590_ = l_Lean_Syntax_isOfKind(v_x_3586_, v___x_3589_);
    if v___x_3590_ == 0 {
        let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3586_);
        v___x_3591_ = lean_box(1);
        v___x_3592_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3592_, 0, v___x_3591_);
        lean_ctor_set(v___x_3592_, 1, v_a_3588_);
        return v___x_3592_;
    } else {
        let mut v_quotContext_3593_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3594_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3595_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3600_: u8 = 0;
        let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_3593_ = lean_ctor_get(v_a_3587_, 1);
        v_currMacroScope_3594_ = lean_ctor_get(v_a_3587_, 2);
        v_ref_3595_ = lean_ctor_get(v_a_3587_, 5);
        v___x_3596_ = lean_unsigned_to_nat(0);
        v___x_3597_ = l_Lean_Syntax_getArg(v_x_3586_, v___x_3596_);
        v___x_3598_ = lean_unsigned_to_nat(2);
        v___x_3599_ = l_Lean_Syntax_getArg(v_x_3586_, v___x_3598_);
        lean_dec(v_x_3586_);
        v___x_3600_ = 0;
        v___x_3601_ = l_Lean_SourceInfo_fromRef(v_ref_3595_, v___x_3600_);
        v___x_3602_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_3603_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2295____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2295____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1,
        );
        v___x_3604_ = l___aux__Init__Core______macroRules__term___u2295____1___closed__2;
        lean_inc(v_currMacroScope_3594_);
        lean_inc(v_quotContext_3593_);
        v___x_3605_ =
            l_Lean_addMacroScope(v_quotContext_3593_, v___x_3604_, v_currMacroScope_3594_);
        v___x_3606_ = l___aux__Init__Core______macroRules__term___u2295____1___closed__6;
        lean_inc_n(v___x_3601_, 2);
        v___x_3607_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3607_, 0, v___x_3601_);
        lean_ctor_set(v___x_3607_, 1, v___x_3603_);
        lean_ctor_set(v___x_3607_, 2, v___x_3605_);
        lean_ctor_set(v___x_3607_, 3, v___x_3606_);
        v___x_3608_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_3609_ = l_Lean_Syntax_node2(v___x_3601_, v___x_3608_, v___x_3597_, v___x_3599_);
        v___x_3610_ = l_Lean_Syntax_node2(v___x_3601_, v___x_3602_, v___x_3607_, v___x_3609_);
        v___x_3611_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3611_, 0, v___x_3610_);
        lean_ctor_set(v___x_3611_, 1, v_a_3588_);
        return v___x_3611_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2295____1___boxed(
    mut v_x_3612_: *mut LeanObject,
    mut v_a_3613_: *mut LeanObject,
    mut v_a_3614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3615_: *mut LeanObject = core::ptr::null_mut();
    v_res_3615_ =
        l___aux__Init__Core______macroRules__term___u2295____1(v_x_3612_, v_a_3613_, v_a_3614_);
    lean_dec_ref(v_a_3613_);
    return v_res_3615_;
}
pub unsafe fn l___aux__Init__Core______unexpand__Sum__1(
    mut v_x_3616_: *mut LeanObject,
    mut v_a_3617_: *mut LeanObject,
    mut v_a_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: u8 = 0;
    v___x_3619_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_3616_);
    v___x_3620_ = l_Lean_Syntax_isOfKind(v_x_3616_, v___x_3619_);
    if v___x_3620_ == 0 {
        let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3616_);
        v___x_3621_ = lean_box(0);
        v___x_3622_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3622_, 0, v___x_3621_);
        lean_ctor_set(v___x_3622_, 1, v_a_3618_);
        return v___x_3622_;
    } else {
        let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3626_: u8 = 0;
        v___x_3623_ = lean_unsigned_to_nat(0);
        v___x_3624_ = l_Lean_Syntax_getArg(v_x_3616_, v___x_3623_);
        v___x_3625_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_3624_);
        v___x_3626_ = l_Lean_Syntax_isOfKind(v___x_3624_, v___x_3625_);
        if v___x_3626_ == 0 {
            let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_3624_);
            lean_dec(v_x_3616_);
            v___x_3627_ = lean_box(0);
            v___x_3628_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_3628_, 0, v___x_3627_);
            lean_ctor_set(v___x_3628_, 1, v_a_3618_);
            return v___x_3628_;
        } else {
            let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3632_: u8 = 0;
            v___x_3629_ = lean_unsigned_to_nat(1);
            v___x_3630_ = l_Lean_Syntax_getArg(v_x_3616_, v___x_3629_);
            lean_dec(v_x_3616_);
            v___x_3631_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_3630_);
            v___x_3632_ = l_Lean_Syntax_matchesNull(v___x_3630_, v___x_3631_);
            if v___x_3632_ == 0 {
                let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_3630_);
                lean_dec(v___x_3624_);
                v___x_3633_ = lean_box(0);
                v___x_3634_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3634_, 0, v___x_3633_);
                lean_ctor_set(v___x_3634_, 1, v_a_3618_);
                return v___x_3634_;
            } else {
                let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_3637_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3638_: u8 = 0;
                let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
                v___x_3635_ = l_Lean_Syntax_getArg(v___x_3630_, v___x_3623_);
                v___x_3636_ = l_Lean_Syntax_getArg(v___x_3630_, v___x_3629_);
                lean_dec(v___x_3630_);
                v_ref_3637_ = l_Lean_replaceRef(v___x_3624_, v_a_3617_);
                lean_dec(v___x_3624_);
                v___x_3638_ = 0;
                v___x_3639_ = l_Lean_SourceInfo_fromRef(v_ref_3637_, v___x_3638_);
                lean_dec(v_ref_3637_);
                v___x_3640_ = l_term___u2295___00__closed__1;
                v___x_3641_ = l_term___u2295___00__closed__2;
                lean_inc(v___x_3639_);
                v___x_3642_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3642_, 0, v___x_3639_);
                lean_ctor_set(v___x_3642_, 1, v___x_3641_);
                v___x_3643_ = l_Lean_Syntax_node3(
                    v___x_3639_,
                    v___x_3640_,
                    v___x_3635_,
                    v___x_3642_,
                    v___x_3636_,
                );
                v___x_3644_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                lean_ctor_set(v___x_3644_, 1, v_a_3618_);
                return v___x_3644_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__Sum__1___boxed(
    mut v_x_3645_: *mut LeanObject,
    mut v_a_3646_: *mut LeanObject,
    mut v_a_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3648_: *mut LeanObject = core::ptr::null_mut();
    v_res_3648_ = l___aux__Init__Core______unexpand__Sum__1(v_x_3645_, v_a_3646_, v_a_3647_);
    lean_dec(v_a_3646_);
    return v_res_3648_;
}
pub unsafe fn l_PSum_ctorIdx___redArg(mut v_x_3649_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_3649_) == 0 {
        let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
        v___x_3650_ = lean_unsigned_to_nat(0);
        return v___x_3650_;
    } else {
        let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
        v___x_3651_ = lean_unsigned_to_nat(1);
        return v___x_3651_;
    }
}
pub unsafe fn l_PSum_ctorIdx___redArg___boxed(mut v_x_3652_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3653_: *mut LeanObject = core::ptr::null_mut();
    v_res_3653_ = l_PSum_ctorIdx___redArg(v_x_3652_);
    lean_dec_ref(v_x_3652_);
    return v_res_3653_;
}
pub unsafe fn l_PSum_ctorIdx(
    mut v_00_u03b1_3654_: *mut LeanObject,
    mut v_00_u03b2_3655_: *mut LeanObject,
    mut v_x_3656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    v___x_3657_ = l_PSum_ctorIdx___redArg(v_x_3656_);
    return v___x_3657_;
}
pub unsafe fn l_PSum_ctorIdx___boxed(
    mut v_00_u03b1_3658_: *mut LeanObject,
    mut v_00_u03b2_3659_: *mut LeanObject,
    mut v_x_3660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3661_: *mut LeanObject = core::ptr::null_mut();
    v_res_3661_ = l_PSum_ctorIdx(v_00_u03b1_3658_, v_00_u03b2_3659_, v_x_3660_);
    lean_dec_ref(v_x_3660_);
    return v_res_3661_;
}
pub unsafe fn l_PSum_ctorElim___redArg(
    mut v_t_3662_: *mut LeanObject,
    mut v_k_3663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    v_val_3664_ = lean_ctor_get(v_t_3662_, 0);
    lean_inc(v_val_3664_);
    lean_dec_ref(v_t_3662_);
    v___x_3665_ = lean_apply_1(v_k_3663_, v_val_3664_);
    return v___x_3665_;
}
pub unsafe fn l_PSum_ctorElim(
    mut v_00_u03b1_3666_: *mut LeanObject,
    mut v_00_u03b2_3667_: *mut LeanObject,
    mut v_motive_3668_: *mut LeanObject,
    mut v_ctorIdx_3669_: *mut LeanObject,
    mut v_t_3670_: *mut LeanObject,
    mut v_h_3671_: *mut LeanObject,
    mut v_k_3672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    v___x_3673_ = l_PSum_ctorElim___redArg(v_t_3670_, v_k_3672_);
    return v___x_3673_;
}
pub unsafe fn l_PSum_ctorElim___boxed(
    mut v_00_u03b1_3674_: *mut LeanObject,
    mut v_00_u03b2_3675_: *mut LeanObject,
    mut v_motive_3676_: *mut LeanObject,
    mut v_ctorIdx_3677_: *mut LeanObject,
    mut v_t_3678_: *mut LeanObject,
    mut v_h_3679_: *mut LeanObject,
    mut v_k_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3681_: *mut LeanObject = core::ptr::null_mut();
    v_res_3681_ = l_PSum_ctorElim(
        v_00_u03b1_3674_,
        v_00_u03b2_3675_,
        v_motive_3676_,
        v_ctorIdx_3677_,
        v_t_3678_,
        v_h_3679_,
        v_k_3680_,
    );
    lean_dec(v_ctorIdx_3677_);
    return v_res_3681_;
}
pub unsafe fn l_PSum_inl_elim___redArg(
    mut v_t_3682_: *mut LeanObject,
    mut v_inl_3683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    v___x_3684_ = l_PSum_ctorElim___redArg(v_t_3682_, v_inl_3683_);
    return v___x_3684_;
}
pub unsafe fn l_PSum_inl_elim(
    mut v_00_u03b1_3685_: *mut LeanObject,
    mut v_00_u03b2_3686_: *mut LeanObject,
    mut v_motive_3687_: *mut LeanObject,
    mut v_t_3688_: *mut LeanObject,
    mut v_h_3689_: *mut LeanObject,
    mut v_inl_3690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    v___x_3691_ = l_PSum_ctorElim___redArg(v_t_3688_, v_inl_3690_);
    return v___x_3691_;
}
pub unsafe fn l_PSum_inr_elim___redArg(
    mut v_t_3692_: *mut LeanObject,
    mut v_inr_3693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    v___x_3694_ = l_PSum_ctorElim___redArg(v_t_3692_, v_inr_3693_);
    return v___x_3694_;
}
pub unsafe fn l_PSum_inr_elim(
    mut v_00_u03b1_3695_: *mut LeanObject,
    mut v_00_u03b2_3696_: *mut LeanObject,
    mut v_motive_3697_: *mut LeanObject,
    mut v_t_3698_: *mut LeanObject,
    mut v_h_3699_: *mut LeanObject,
    mut v_inr_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3701_ = l_PSum_ctorElim___redArg(v_t_3698_, v_inr_3700_);
    return v___x_3701_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1()
-> *mut LeanObject {
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    v___x_3719_ = l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0;
    v___x_3720_ = l_String_toRawSubstring_x27(v___x_3719_);
    return v___x_3720_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2295_x27____1(
    mut v_x_3734_: *mut LeanObject,
    mut v_a_3735_: *mut LeanObject,
    mut v_a_3736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    v___x_3737_ = l_term___u2295_x27___00__closed__1;
    lean_inc(v_x_3734_);
    v___x_3738_ = l_Lean_Syntax_isOfKind(v_x_3734_, v___x_3737_);
    if v___x_3738_ == 0 {
        let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3734_);
        v___x_3739_ = lean_box(1);
        v___x_3740_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3740_, 0, v___x_3739_);
        lean_ctor_set(v___x_3740_, 1, v_a_3736_);
        return v___x_3740_;
    } else {
        let mut v_quotContext_3741_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3742_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_3743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3748_: u8 = 0;
        let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_3741_ = lean_ctor_get(v_a_3735_, 1);
        v_currMacroScope_3742_ = lean_ctor_get(v_a_3735_, 2);
        v_ref_3743_ = lean_ctor_get(v_a_3735_, 5);
        v___x_3744_ = lean_unsigned_to_nat(0);
        v___x_3745_ = l_Lean_Syntax_getArg(v_x_3734_, v___x_3744_);
        v___x_3746_ = lean_unsigned_to_nat(2);
        v___x_3747_ = l_Lean_Syntax_getArg(v_x_3734_, v___x_3746_);
        lean_dec(v_x_3734_);
        v___x_3748_ = 0;
        v___x_3749_ = l_Lean_SourceInfo_fromRef(v_ref_3743_, v___x_3748_);
        v___x_3750_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_3751_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1,
        );
        v___x_3752_ = l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2;
        lean_inc(v_currMacroScope_3742_);
        lean_inc(v_quotContext_3741_);
        v___x_3753_ =
            l_Lean_addMacroScope(v_quotContext_3741_, v___x_3752_, v_currMacroScope_3742_);
        v___x_3754_ = l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6;
        lean_inc_n(v___x_3749_, 2);
        v___x_3755_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_3755_, 0, v___x_3749_);
        lean_ctor_set(v___x_3755_, 1, v___x_3751_);
        lean_ctor_set(v___x_3755_, 2, v___x_3753_);
        lean_ctor_set(v___x_3755_, 3, v___x_3754_);
        v___x_3756_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_3757_ = l_Lean_Syntax_node2(v___x_3749_, v___x_3756_, v___x_3745_, v___x_3747_);
        v___x_3758_ = l_Lean_Syntax_node2(v___x_3749_, v___x_3750_, v___x_3755_, v___x_3757_);
        v___x_3759_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3759_, 0, v___x_3758_);
        lean_ctor_set(v___x_3759_, 1, v_a_3736_);
        return v___x_3759_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2295_x27____1___boxed(
    mut v_x_3760_: *mut LeanObject,
    mut v_a_3761_: *mut LeanObject,
    mut v_a_3762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3763_: *mut LeanObject = core::ptr::null_mut();
    v_res_3763_ =
        l___aux__Init__Core______macroRules__term___u2295_x27____1(v_x_3760_, v_a_3761_, v_a_3762_);
    lean_dec_ref(v_a_3761_);
    return v_res_3763_;
}
pub unsafe fn l___aux__Init__Core______unexpand__PSum__1(
    mut v_x_3764_: *mut LeanObject,
    mut v_a_3765_: *mut LeanObject,
    mut v_a_3766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: u8 = 0;
    v___x_3767_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_3764_);
    v___x_3768_ = l_Lean_Syntax_isOfKind(v_x_3764_, v___x_3767_);
    if v___x_3768_ == 0 {
        let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3764_);
        v___x_3769_ = lean_box(0);
        v___x_3770_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3770_, 0, v___x_3769_);
        lean_ctor_set(v___x_3770_, 1, v_a_3766_);
        return v___x_3770_;
    } else {
        let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3774_: u8 = 0;
        v___x_3771_ = lean_unsigned_to_nat(0);
        v___x_3772_ = l_Lean_Syntax_getArg(v_x_3764_, v___x_3771_);
        v___x_3773_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_3772_);
        v___x_3774_ = l_Lean_Syntax_isOfKind(v___x_3772_, v___x_3773_);
        if v___x_3774_ == 0 {
            let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_3772_);
            lean_dec(v_x_3764_);
            v___x_3775_ = lean_box(0);
            v___x_3776_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_3776_, 0, v___x_3775_);
            lean_ctor_set(v___x_3776_, 1, v_a_3766_);
            return v___x_3776_;
        } else {
            let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3780_: u8 = 0;
            v___x_3777_ = lean_unsigned_to_nat(1);
            v___x_3778_ = l_Lean_Syntax_getArg(v_x_3764_, v___x_3777_);
            lean_dec(v_x_3764_);
            v___x_3779_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_3778_);
            v___x_3780_ = l_Lean_Syntax_matchesNull(v___x_3778_, v___x_3779_);
            if v___x_3780_ == 0 {
                let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_3778_);
                lean_dec(v___x_3772_);
                v___x_3781_ = lean_box(0);
                v___x_3782_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3782_, 0, v___x_3781_);
                lean_ctor_set(v___x_3782_, 1, v_a_3766_);
                return v___x_3782_;
            } else {
                let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_3785_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3786_: u8 = 0;
                let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
                v___x_3783_ = l_Lean_Syntax_getArg(v___x_3778_, v___x_3771_);
                v___x_3784_ = l_Lean_Syntax_getArg(v___x_3778_, v___x_3777_);
                lean_dec(v___x_3778_);
                v_ref_3785_ = l_Lean_replaceRef(v___x_3772_, v_a_3765_);
                lean_dec(v___x_3772_);
                v___x_3786_ = 0;
                v___x_3787_ = l_Lean_SourceInfo_fromRef(v_ref_3785_, v___x_3786_);
                lean_dec(v_ref_3785_);
                v___x_3788_ = l_term___u2295_x27___00__closed__1;
                v___x_3789_ = l_term___u2295_x27___00__closed__2;
                lean_inc(v___x_3787_);
                v___x_3790_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3790_, 0, v___x_3787_);
                lean_ctor_set(v___x_3790_, 1, v___x_3789_);
                v___x_3791_ = l_Lean_Syntax_node3(
                    v___x_3787_,
                    v___x_3788_,
                    v___x_3783_,
                    v___x_3790_,
                    v___x_3784_,
                );
                v___x_3792_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3792_, 0, v___x_3791_);
                lean_ctor_set(v___x_3792_, 1, v_a_3766_);
                return v___x_3792_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__PSum__1___boxed(
    mut v_x_3793_: *mut LeanObject,
    mut v_a_3794_: *mut LeanObject,
    mut v_a_3795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3796_: *mut LeanObject = core::ptr::null_mut();
    v_res_3796_ = l___aux__Init__Core______unexpand__PSum__1(v_x_3793_, v_a_3794_, v_a_3795_);
    lean_dec(v_a_3794_);
    return v_res_3796_;
}
pub unsafe fn l_PSum_inhabitedLeft___redArg(mut v_inst_3797_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    v___x_3798_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3798_, 0, v_inst_3797_);
    return v___x_3798_;
}
pub unsafe fn l_PSum_inhabitedLeft(
    mut v_00_u03b1_3799_: *mut LeanObject,
    mut v_00_u03b2_3800_: *mut LeanObject,
    mut v_inst_3801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    v___x_3802_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3802_, 0, v_inst_3801_);
    return v___x_3802_;
}
pub unsafe fn l_PSum_inhabitedRight___redArg(mut v_inst_3803_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    v___x_3804_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3804_, 0, v_inst_3803_);
    return v___x_3804_;
}
pub unsafe fn l_PSum_inhabitedRight(
    mut v_00_u03b1_3805_: *mut LeanObject,
    mut v_00_u03b2_3806_: *mut LeanObject,
    mut v_inst_3807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    v___x_3808_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3808_, 0, v_inst_3807_);
    return v___x_3808_;
}
pub unsafe fn l_ForInStep_ctorIdx___redArg(mut v_x_3809_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_3809_) == 0 {
        let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
        v___x_3810_ = lean_unsigned_to_nat(0);
        return v___x_3810_;
    } else {
        let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
        v___x_3811_ = lean_unsigned_to_nat(1);
        return v___x_3811_;
    }
}
pub unsafe fn l_ForInStep_ctorIdx___redArg___boxed(
    mut v_x_3812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3813_: *mut LeanObject = core::ptr::null_mut();
    v_res_3813_ = l_ForInStep_ctorIdx___redArg(v_x_3812_);
    lean_dec_ref(v_x_3812_);
    return v_res_3813_;
}
pub unsafe fn l_ForInStep_ctorIdx(
    mut v_00_u03b1_3814_: *mut LeanObject,
    mut v_x_3815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    v___x_3816_ = l_ForInStep_ctorIdx___redArg(v_x_3815_);
    return v___x_3816_;
}
pub unsafe fn l_ForInStep_ctorIdx___boxed(
    mut v_00_u03b1_3817_: *mut LeanObject,
    mut v_x_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3819_: *mut LeanObject = core::ptr::null_mut();
    v_res_3819_ = l_ForInStep_ctorIdx(v_00_u03b1_3817_, v_x_3818_);
    lean_dec_ref(v_x_3818_);
    return v_res_3819_;
}
pub unsafe fn l_ForInStep_ctorElim___redArg(
    mut v_t_3820_: *mut LeanObject,
    mut v_k_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    v_a_3822_ = lean_ctor_get(v_t_3820_, 0);
    lean_inc(v_a_3822_);
    lean_dec_ref(v_t_3820_);
    v___x_3823_ = lean_apply_1(v_k_3821_, v_a_3822_);
    return v___x_3823_;
}
pub unsafe fn l_ForInStep_ctorElim(
    mut v_00_u03b1_3824_: *mut LeanObject,
    mut v_motive_3825_: *mut LeanObject,
    mut v_ctorIdx_3826_: *mut LeanObject,
    mut v_t_3827_: *mut LeanObject,
    mut v_h_3828_: *mut LeanObject,
    mut v_k_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    v___x_3830_ = l_ForInStep_ctorElim___redArg(v_t_3827_, v_k_3829_);
    return v___x_3830_;
}
pub unsafe fn l_ForInStep_ctorElim___boxed(
    mut v_00_u03b1_3831_: *mut LeanObject,
    mut v_motive_3832_: *mut LeanObject,
    mut v_ctorIdx_3833_: *mut LeanObject,
    mut v_t_3834_: *mut LeanObject,
    mut v_h_3835_: *mut LeanObject,
    mut v_k_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3837_: *mut LeanObject = core::ptr::null_mut();
    v_res_3837_ = l_ForInStep_ctorElim(
        v_00_u03b1_3831_,
        v_motive_3832_,
        v_ctorIdx_3833_,
        v_t_3834_,
        v_h_3835_,
        v_k_3836_,
    );
    lean_dec(v_ctorIdx_3833_);
    return v_res_3837_;
}
pub unsafe fn l_ForInStep_done_elim___redArg(
    mut v_t_3838_: *mut LeanObject,
    mut v_done_3839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    v___x_3840_ = l_ForInStep_ctorElim___redArg(v_t_3838_, v_done_3839_);
    return v___x_3840_;
}
pub unsafe fn l_ForInStep_done_elim(
    mut v_00_u03b1_3841_: *mut LeanObject,
    mut v_motive_3842_: *mut LeanObject,
    mut v_t_3843_: *mut LeanObject,
    mut v_h_3844_: *mut LeanObject,
    mut v_done_3845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    v___x_3846_ = l_ForInStep_ctorElim___redArg(v_t_3843_, v_done_3845_);
    return v___x_3846_;
}
pub unsafe fn l_ForInStep_yield_elim___redArg(
    mut v_t_3847_: *mut LeanObject,
    mut v_yield_3848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    v___x_3849_ = l_ForInStep_ctorElim___redArg(v_t_3847_, v_yield_3848_);
    return v___x_3849_;
}
pub unsafe fn l_ForInStep_yield_elim(
    mut v_00_u03b1_3850_: *mut LeanObject,
    mut v_motive_3851_: *mut LeanObject,
    mut v_t_3852_: *mut LeanObject,
    mut v_h_3853_: *mut LeanObject,
    mut v_yield_3854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    v___x_3855_ = l_ForInStep_ctorElim___redArg(v_t_3852_, v_yield_3854_);
    return v___x_3855_;
}
pub unsafe fn l_instInhabitedForInStep_default___redArg(
    mut v_inst_3856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    v___x_3857_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3857_, 0, v_inst_3856_);
    return v___x_3857_;
}
pub unsafe fn l_instInhabitedForInStep_default(
    mut v_00_u03b1_3858_: *mut LeanObject,
    mut v_inst_3859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    v___x_3860_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3860_, 0, v_inst_3859_);
    return v___x_3860_;
}
pub unsafe fn l_instInhabitedForInStep___redArg(
    mut v_inst_3861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    v___x_3862_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3862_, 0, v_inst_3861_);
    return v___x_3862_;
}
pub unsafe fn l_instInhabitedForInStep(
    mut v_a_3863_: *mut LeanObject,
    mut v_inst_3864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    v___x_3865_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3865_, 0, v_inst_3864_);
    return v___x_3865_;
}
pub unsafe fn l_DoResultPRBC_ctorIdx___redArg(mut v_x_3866_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_3866_) {
        0 => {
            let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
            v___x_3867_ = lean_unsigned_to_nat(0);
            return v___x_3867_;
        }
        1 => {
            let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
            v___x_3868_ = lean_unsigned_to_nat(1);
            return v___x_3868_;
        }
        2 => {
            let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
            v___x_3869_ = lean_unsigned_to_nat(2);
            return v___x_3869_;
        }
        _ => {
            let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
            v___x_3870_ = lean_unsigned_to_nat(3);
            return v___x_3870_;
        }
    }
}
pub unsafe fn l_DoResultPRBC_ctorIdx___redArg___boxed(
    mut v_x_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3872_: *mut LeanObject = core::ptr::null_mut();
    v_res_3872_ = l_DoResultPRBC_ctorIdx___redArg(v_x_3871_);
    lean_dec_ref(v_x_3871_);
    return v_res_3872_;
}
pub unsafe fn l_DoResultPRBC_ctorIdx(
    mut v_00_u03b1_3873_: *mut LeanObject,
    mut v_00_u03b2_3874_: *mut LeanObject,
    mut v_00_u03c3_3875_: *mut LeanObject,
    mut v_x_3876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    v___x_3877_ = l_DoResultPRBC_ctorIdx___redArg(v_x_3876_);
    return v___x_3877_;
}
pub unsafe fn l_DoResultPRBC_ctorIdx___boxed(
    mut v_00_u03b1_3878_: *mut LeanObject,
    mut v_00_u03b2_3879_: *mut LeanObject,
    mut v_00_u03c3_3880_: *mut LeanObject,
    mut v_x_3881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3882_: *mut LeanObject = core::ptr::null_mut();
    v_res_3882_ = l_DoResultPRBC_ctorIdx(
        v_00_u03b1_3878_,
        v_00_u03b2_3879_,
        v_00_u03c3_3880_,
        v_x_3881_,
    );
    lean_dec_ref(v_x_3881_);
    return v_res_3882_;
}
pub unsafe fn l_DoResultPRBC_ctorElim___redArg(
    mut v_t_3883_: *mut LeanObject,
    mut v_k_3884_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_3883_) {
        2 => {
            let mut v_a_3885_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
            v_a_3885_ = lean_ctor_get(v_t_3883_, 0);
            lean_inc(v_a_3885_);
            lean_dec_ref_known(v_t_3883_, 1);
            v___x_3886_ = lean_apply_1(v_k_3884_, v_a_3885_);
            return v___x_3886_;
        }
        3 => {
            let mut v_a_3887_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
            v_a_3887_ = lean_ctor_get(v_t_3883_, 0);
            lean_inc(v_a_3887_);
            lean_dec_ref_known(v_t_3883_, 1);
            v___x_3888_ = lean_apply_1(v_k_3884_, v_a_3887_);
            return v___x_3888_;
        }
        _ => {
            let mut v_a_3889_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_3890_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
            v_a_3889_ = lean_ctor_get(v_t_3883_, 0);
            lean_inc(v_a_3889_);
            v_a_3890_ = lean_ctor_get(v_t_3883_, 1);
            lean_inc(v_a_3890_);
            lean_dec_ref(v_t_3883_);
            v___x_3891_ = lean_apply_2(v_k_3884_, v_a_3889_, v_a_3890_);
            return v___x_3891_;
        }
    }
}
pub unsafe fn l_DoResultPRBC_ctorElim(
    mut v_00_u03b1_3892_: *mut LeanObject,
    mut v_00_u03b2_3893_: *mut LeanObject,
    mut v_00_u03c3_3894_: *mut LeanObject,
    mut v_motive_3895_: *mut LeanObject,
    mut v_ctorIdx_3896_: *mut LeanObject,
    mut v_t_3897_: *mut LeanObject,
    mut v_h_3898_: *mut LeanObject,
    mut v_k_3899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    v___x_3900_ = l_DoResultPRBC_ctorElim___redArg(v_t_3897_, v_k_3899_);
    return v___x_3900_;
}
pub unsafe fn l_DoResultPRBC_ctorElim___boxed(
    mut v_00_u03b1_3901_: *mut LeanObject,
    mut v_00_u03b2_3902_: *mut LeanObject,
    mut v_00_u03c3_3903_: *mut LeanObject,
    mut v_motive_3904_: *mut LeanObject,
    mut v_ctorIdx_3905_: *mut LeanObject,
    mut v_t_3906_: *mut LeanObject,
    mut v_h_3907_: *mut LeanObject,
    mut v_k_3908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3909_: *mut LeanObject = core::ptr::null_mut();
    v_res_3909_ = l_DoResultPRBC_ctorElim(
        v_00_u03b1_3901_,
        v_00_u03b2_3902_,
        v_00_u03c3_3903_,
        v_motive_3904_,
        v_ctorIdx_3905_,
        v_t_3906_,
        v_h_3907_,
        v_k_3908_,
    );
    lean_dec(v_ctorIdx_3905_);
    return v_res_3909_;
}
pub unsafe fn l_DoResultPRBC_pure_elim___redArg(
    mut v_t_3910_: *mut LeanObject,
    mut v_pure_3911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    v___x_3912_ = l_DoResultPRBC_ctorElim___redArg(v_t_3910_, v_pure_3911_);
    return v___x_3912_;
}
pub unsafe fn l_DoResultPRBC_pure_elim(
    mut v_00_u03b1_3913_: *mut LeanObject,
    mut v_00_u03b2_3914_: *mut LeanObject,
    mut v_00_u03c3_3915_: *mut LeanObject,
    mut v_motive_3916_: *mut LeanObject,
    mut v_t_3917_: *mut LeanObject,
    mut v_h_3918_: *mut LeanObject,
    mut v_pure_3919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    v___x_3920_ = l_DoResultPRBC_ctorElim___redArg(v_t_3917_, v_pure_3919_);
    return v___x_3920_;
}
pub unsafe fn l_DoResultPRBC_return_elim___redArg(
    mut v_t_3921_: *mut LeanObject,
    mut v_return_3922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    v___x_3923_ = l_DoResultPRBC_ctorElim___redArg(v_t_3921_, v_return_3922_);
    return v___x_3923_;
}
pub unsafe fn l_DoResultPRBC_return_elim(
    mut v_00_u03b1_3924_: *mut LeanObject,
    mut v_00_u03b2_3925_: *mut LeanObject,
    mut v_00_u03c3_3926_: *mut LeanObject,
    mut v_motive_3927_: *mut LeanObject,
    mut v_t_3928_: *mut LeanObject,
    mut v_h_3929_: *mut LeanObject,
    mut v_return_3930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    v___x_3931_ = l_DoResultPRBC_ctorElim___redArg(v_t_3928_, v_return_3930_);
    return v___x_3931_;
}
pub unsafe fn l_DoResultPRBC_break_elim___redArg(
    mut v_t_3932_: *mut LeanObject,
    mut v_break_3933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    v___x_3934_ = l_DoResultPRBC_ctorElim___redArg(v_t_3932_, v_break_3933_);
    return v___x_3934_;
}
pub unsafe fn l_DoResultPRBC_break_elim(
    mut v_00_u03b1_3935_: *mut LeanObject,
    mut v_00_u03b2_3936_: *mut LeanObject,
    mut v_00_u03c3_3937_: *mut LeanObject,
    mut v_motive_3938_: *mut LeanObject,
    mut v_t_3939_: *mut LeanObject,
    mut v_h_3940_: *mut LeanObject,
    mut v_break_3941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    v___x_3942_ = l_DoResultPRBC_ctorElim___redArg(v_t_3939_, v_break_3941_);
    return v___x_3942_;
}
pub unsafe fn l_DoResultPRBC_continue_elim___redArg(
    mut v_t_3943_: *mut LeanObject,
    mut v_continue_3944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    v___x_3945_ = l_DoResultPRBC_ctorElim___redArg(v_t_3943_, v_continue_3944_);
    return v___x_3945_;
}
pub unsafe fn l_DoResultPRBC_continue_elim(
    mut v_00_u03b1_3946_: *mut LeanObject,
    mut v_00_u03b2_3947_: *mut LeanObject,
    mut v_00_u03c3_3948_: *mut LeanObject,
    mut v_motive_3949_: *mut LeanObject,
    mut v_t_3950_: *mut LeanObject,
    mut v_h_3951_: *mut LeanObject,
    mut v_continue_3952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    v___x_3953_ = l_DoResultPRBC_ctorElim___redArg(v_t_3950_, v_continue_3952_);
    return v___x_3953_;
}
pub unsafe fn l_DoResultPR_ctorIdx___redArg(mut v_x_3954_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_3954_) == 0 {
        let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
        v___x_3955_ = lean_unsigned_to_nat(0);
        return v___x_3955_;
    } else {
        let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
        v___x_3956_ = lean_unsigned_to_nat(1);
        return v___x_3956_;
    }
}
pub unsafe fn l_DoResultPR_ctorIdx___redArg___boxed(
    mut v_x_3957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3958_: *mut LeanObject = core::ptr::null_mut();
    v_res_3958_ = l_DoResultPR_ctorIdx___redArg(v_x_3957_);
    lean_dec_ref(v_x_3957_);
    return v_res_3958_;
}
pub unsafe fn l_DoResultPR_ctorIdx(
    mut v_00_u03b1_3959_: *mut LeanObject,
    mut v_00_u03b2_3960_: *mut LeanObject,
    mut v_00_u03c3_3961_: *mut LeanObject,
    mut v_x_3962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    v___x_3963_ = l_DoResultPR_ctorIdx___redArg(v_x_3962_);
    return v___x_3963_;
}
pub unsafe fn l_DoResultPR_ctorIdx___boxed(
    mut v_00_u03b1_3964_: *mut LeanObject,
    mut v_00_u03b2_3965_: *mut LeanObject,
    mut v_00_u03c3_3966_: *mut LeanObject,
    mut v_x_3967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3968_: *mut LeanObject = core::ptr::null_mut();
    v_res_3968_ = l_DoResultPR_ctorIdx(
        v_00_u03b1_3964_,
        v_00_u03b2_3965_,
        v_00_u03c3_3966_,
        v_x_3967_,
    );
    lean_dec_ref(v_x_3967_);
    return v_res_3968_;
}
pub unsafe fn l_DoResultPR_ctorElim___redArg(
    mut v_t_3969_: *mut LeanObject,
    mut v_k_3970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    v_a_3971_ = lean_ctor_get(v_t_3969_, 0);
    lean_inc(v_a_3971_);
    v_a_3972_ = lean_ctor_get(v_t_3969_, 1);
    lean_inc(v_a_3972_);
    lean_dec_ref(v_t_3969_);
    v___x_3973_ = lean_apply_2(v_k_3970_, v_a_3971_, v_a_3972_);
    return v___x_3973_;
}
pub unsafe fn l_DoResultPR_ctorElim(
    mut v_00_u03b1_3974_: *mut LeanObject,
    mut v_00_u03b2_3975_: *mut LeanObject,
    mut v_00_u03c3_3976_: *mut LeanObject,
    mut v_motive_3977_: *mut LeanObject,
    mut v_ctorIdx_3978_: *mut LeanObject,
    mut v_t_3979_: *mut LeanObject,
    mut v_h_3980_: *mut LeanObject,
    mut v_k_3981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    v___x_3982_ = l_DoResultPR_ctorElim___redArg(v_t_3979_, v_k_3981_);
    return v___x_3982_;
}
pub unsafe fn l_DoResultPR_ctorElim___boxed(
    mut v_00_u03b1_3983_: *mut LeanObject,
    mut v_00_u03b2_3984_: *mut LeanObject,
    mut v_00_u03c3_3985_: *mut LeanObject,
    mut v_motive_3986_: *mut LeanObject,
    mut v_ctorIdx_3987_: *mut LeanObject,
    mut v_t_3988_: *mut LeanObject,
    mut v_h_3989_: *mut LeanObject,
    mut v_k_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3991_: *mut LeanObject = core::ptr::null_mut();
    v_res_3991_ = l_DoResultPR_ctorElim(
        v_00_u03b1_3983_,
        v_00_u03b2_3984_,
        v_00_u03c3_3985_,
        v_motive_3986_,
        v_ctorIdx_3987_,
        v_t_3988_,
        v_h_3989_,
        v_k_3990_,
    );
    lean_dec(v_ctorIdx_3987_);
    return v_res_3991_;
}
pub unsafe fn l_DoResultPR_pure_elim___redArg(
    mut v_t_3992_: *mut LeanObject,
    mut v_pure_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    v___x_3994_ = l_DoResultPR_ctorElim___redArg(v_t_3992_, v_pure_3993_);
    return v___x_3994_;
}
pub unsafe fn l_DoResultPR_pure_elim(
    mut v_00_u03b1_3995_: *mut LeanObject,
    mut v_00_u03b2_3996_: *mut LeanObject,
    mut v_00_u03c3_3997_: *mut LeanObject,
    mut v_motive_3998_: *mut LeanObject,
    mut v_t_3999_: *mut LeanObject,
    mut v_h_4000_: *mut LeanObject,
    mut v_pure_4001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    v___x_4002_ = l_DoResultPR_ctorElim___redArg(v_t_3999_, v_pure_4001_);
    return v___x_4002_;
}
pub unsafe fn l_DoResultPR_return_elim___redArg(
    mut v_t_4003_: *mut LeanObject,
    mut v_return_4004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    v___x_4005_ = l_DoResultPR_ctorElim___redArg(v_t_4003_, v_return_4004_);
    return v___x_4005_;
}
pub unsafe fn l_DoResultPR_return_elim(
    mut v_00_u03b1_4006_: *mut LeanObject,
    mut v_00_u03b2_4007_: *mut LeanObject,
    mut v_00_u03c3_4008_: *mut LeanObject,
    mut v_motive_4009_: *mut LeanObject,
    mut v_t_4010_: *mut LeanObject,
    mut v_h_4011_: *mut LeanObject,
    mut v_return_4012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    v___x_4013_ = l_DoResultPR_ctorElim___redArg(v_t_4010_, v_return_4012_);
    return v___x_4013_;
}
pub unsafe fn l_DoResultBC_ctorIdx___redArg(mut v_x_4014_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_4014_) == 0 {
        let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
        v___x_4015_ = lean_unsigned_to_nat(0);
        return v___x_4015_;
    } else {
        let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
        v___x_4016_ = lean_unsigned_to_nat(1);
        return v___x_4016_;
    }
}
pub unsafe fn l_DoResultBC_ctorIdx___redArg___boxed(
    mut v_x_4017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4018_: *mut LeanObject = core::ptr::null_mut();
    v_res_4018_ = l_DoResultBC_ctorIdx___redArg(v_x_4017_);
    lean_dec_ref(v_x_4017_);
    return v_res_4018_;
}
pub unsafe fn l_DoResultBC_ctorIdx(
    mut v_00_u03c3_4019_: *mut LeanObject,
    mut v_x_4020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    v___x_4021_ = l_DoResultBC_ctorIdx___redArg(v_x_4020_);
    return v___x_4021_;
}
pub unsafe fn l_DoResultBC_ctorIdx___boxed(
    mut v_00_u03c3_4022_: *mut LeanObject,
    mut v_x_4023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4024_: *mut LeanObject = core::ptr::null_mut();
    v_res_4024_ = l_DoResultBC_ctorIdx(v_00_u03c3_4022_, v_x_4023_);
    lean_dec_ref(v_x_4023_);
    return v_res_4024_;
}
pub unsafe fn l_DoResultBC_ctorElim___redArg(
    mut v_t_4025_: *mut LeanObject,
    mut v_k_4026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    v_a_4027_ = lean_ctor_get(v_t_4025_, 0);
    lean_inc(v_a_4027_);
    lean_dec_ref(v_t_4025_);
    v___x_4028_ = lean_apply_1(v_k_4026_, v_a_4027_);
    return v___x_4028_;
}
pub unsafe fn l_DoResultBC_ctorElim(
    mut v_00_u03c3_4029_: *mut LeanObject,
    mut v_motive_4030_: *mut LeanObject,
    mut v_ctorIdx_4031_: *mut LeanObject,
    mut v_t_4032_: *mut LeanObject,
    mut v_h_4033_: *mut LeanObject,
    mut v_k_4034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    v___x_4035_ = l_DoResultBC_ctorElim___redArg(v_t_4032_, v_k_4034_);
    return v___x_4035_;
}
pub unsafe fn l_DoResultBC_ctorElim___boxed(
    mut v_00_u03c3_4036_: *mut LeanObject,
    mut v_motive_4037_: *mut LeanObject,
    mut v_ctorIdx_4038_: *mut LeanObject,
    mut v_t_4039_: *mut LeanObject,
    mut v_h_4040_: *mut LeanObject,
    mut v_k_4041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4042_: *mut LeanObject = core::ptr::null_mut();
    v_res_4042_ = l_DoResultBC_ctorElim(
        v_00_u03c3_4036_,
        v_motive_4037_,
        v_ctorIdx_4038_,
        v_t_4039_,
        v_h_4040_,
        v_k_4041_,
    );
    lean_dec(v_ctorIdx_4038_);
    return v_res_4042_;
}
pub unsafe fn l_DoResultBC_break_elim___redArg(
    mut v_t_4043_: *mut LeanObject,
    mut v_break_4044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    v___x_4045_ = l_DoResultBC_ctorElim___redArg(v_t_4043_, v_break_4044_);
    return v___x_4045_;
}
pub unsafe fn l_DoResultBC_break_elim(
    mut v_00_u03c3_4046_: *mut LeanObject,
    mut v_motive_4047_: *mut LeanObject,
    mut v_t_4048_: *mut LeanObject,
    mut v_h_4049_: *mut LeanObject,
    mut v_break_4050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    v___x_4051_ = l_DoResultBC_ctorElim___redArg(v_t_4048_, v_break_4050_);
    return v___x_4051_;
}
pub unsafe fn l_DoResultBC_continue_elim___redArg(
    mut v_t_4052_: *mut LeanObject,
    mut v_continue_4053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    v___x_4054_ = l_DoResultBC_ctorElim___redArg(v_t_4052_, v_continue_4053_);
    return v___x_4054_;
}
pub unsafe fn l_DoResultBC_continue_elim(
    mut v_00_u03c3_4055_: *mut LeanObject,
    mut v_motive_4056_: *mut LeanObject,
    mut v_t_4057_: *mut LeanObject,
    mut v_h_4058_: *mut LeanObject,
    mut v_continue_4059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    v___x_4060_ = l_DoResultBC_ctorElim___redArg(v_t_4057_, v_continue_4059_);
    return v___x_4060_;
}
pub unsafe fn l_DoResultSBC_ctorIdx___redArg(mut v_x_4061_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4061_) {
        0 => {
            let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
            v___x_4062_ = lean_unsigned_to_nat(0);
            return v___x_4062_;
        }
        1 => {
            let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
            v___x_4063_ = lean_unsigned_to_nat(1);
            return v___x_4063_;
        }
        _ => {
            let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
            v___x_4064_ = lean_unsigned_to_nat(2);
            return v___x_4064_;
        }
    }
}
pub unsafe fn l_DoResultSBC_ctorIdx___redArg___boxed(
    mut v_x_4065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4066_: *mut LeanObject = core::ptr::null_mut();
    v_res_4066_ = l_DoResultSBC_ctorIdx___redArg(v_x_4065_);
    lean_dec_ref(v_x_4065_);
    return v_res_4066_;
}
pub unsafe fn l_DoResultSBC_ctorIdx(
    mut v_00_u03b1_4067_: *mut LeanObject,
    mut v_00_u03c3_4068_: *mut LeanObject,
    mut v_x_4069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    v___x_4070_ = l_DoResultSBC_ctorIdx___redArg(v_x_4069_);
    return v___x_4070_;
}
pub unsafe fn l_DoResultSBC_ctorIdx___boxed(
    mut v_00_u03b1_4071_: *mut LeanObject,
    mut v_00_u03c3_4072_: *mut LeanObject,
    mut v_x_4073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4074_: *mut LeanObject = core::ptr::null_mut();
    v_res_4074_ = l_DoResultSBC_ctorIdx(v_00_u03b1_4071_, v_00_u03c3_4072_, v_x_4073_);
    lean_dec_ref(v_x_4073_);
    return v_res_4074_;
}
pub unsafe fn l_DoResultSBC_ctorElim___redArg(
    mut v_t_4075_: *mut LeanObject,
    mut v_k_4076_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4075_) == 0 {
        let mut v_a_4077_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
        v_a_4077_ = lean_ctor_get(v_t_4075_, 0);
        lean_inc(v_a_4077_);
        v_a_4078_ = lean_ctor_get(v_t_4075_, 1);
        lean_inc(v_a_4078_);
        lean_dec_ref_known(v_t_4075_, 2);
        v___x_4079_ = lean_apply_2(v_k_4076_, v_a_4077_, v_a_4078_);
        return v___x_4079_;
    } else {
        let mut v_a_4080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
        v_a_4080_ = lean_ctor_get(v_t_4075_, 0);
        lean_inc(v_a_4080_);
        lean_dec_ref(v_t_4075_);
        v___x_4081_ = lean_apply_1(v_k_4076_, v_a_4080_);
        return v___x_4081_;
    }
}
pub unsafe fn l_DoResultSBC_ctorElim(
    mut v_00_u03b1_4082_: *mut LeanObject,
    mut v_00_u03c3_4083_: *mut LeanObject,
    mut v_motive_4084_: *mut LeanObject,
    mut v_ctorIdx_4085_: *mut LeanObject,
    mut v_t_4086_: *mut LeanObject,
    mut v_h_4087_: *mut LeanObject,
    mut v_k_4088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    v___x_4089_ = l_DoResultSBC_ctorElim___redArg(v_t_4086_, v_k_4088_);
    return v___x_4089_;
}
pub unsafe fn l_DoResultSBC_ctorElim___boxed(
    mut v_00_u03b1_4090_: *mut LeanObject,
    mut v_00_u03c3_4091_: *mut LeanObject,
    mut v_motive_4092_: *mut LeanObject,
    mut v_ctorIdx_4093_: *mut LeanObject,
    mut v_t_4094_: *mut LeanObject,
    mut v_h_4095_: *mut LeanObject,
    mut v_k_4096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4097_: *mut LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_DoResultSBC_ctorElim(
        v_00_u03b1_4090_,
        v_00_u03c3_4091_,
        v_motive_4092_,
        v_ctorIdx_4093_,
        v_t_4094_,
        v_h_4095_,
        v_k_4096_,
    );
    lean_dec(v_ctorIdx_4093_);
    return v_res_4097_;
}
pub unsafe fn l_DoResultSBC_pureReturn_elim___redArg(
    mut v_t_4098_: *mut LeanObject,
    mut v_pureReturn_4099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    v___x_4100_ = l_DoResultSBC_ctorElim___redArg(v_t_4098_, v_pureReturn_4099_);
    return v___x_4100_;
}
pub unsafe fn l_DoResultSBC_pureReturn_elim(
    mut v_00_u03b1_4101_: *mut LeanObject,
    mut v_00_u03c3_4102_: *mut LeanObject,
    mut v_motive_4103_: *mut LeanObject,
    mut v_t_4104_: *mut LeanObject,
    mut v_h_4105_: *mut LeanObject,
    mut v_pureReturn_4106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    v___x_4107_ = l_DoResultSBC_ctorElim___redArg(v_t_4104_, v_pureReturn_4106_);
    return v___x_4107_;
}
pub unsafe fn l_DoResultSBC_break_elim___redArg(
    mut v_t_4108_: *mut LeanObject,
    mut v_break_4109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    v___x_4110_ = l_DoResultSBC_ctorElim___redArg(v_t_4108_, v_break_4109_);
    return v___x_4110_;
}
pub unsafe fn l_DoResultSBC_break_elim(
    mut v_00_u03b1_4111_: *mut LeanObject,
    mut v_00_u03c3_4112_: *mut LeanObject,
    mut v_motive_4113_: *mut LeanObject,
    mut v_t_4114_: *mut LeanObject,
    mut v_h_4115_: *mut LeanObject,
    mut v_break_4116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    v___x_4117_ = l_DoResultSBC_ctorElim___redArg(v_t_4114_, v_break_4116_);
    return v___x_4117_;
}
pub unsafe fn l_DoResultSBC_continue_elim___redArg(
    mut v_t_4118_: *mut LeanObject,
    mut v_continue_4119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    v___x_4120_ = l_DoResultSBC_ctorElim___redArg(v_t_4118_, v_continue_4119_);
    return v___x_4120_;
}
pub unsafe fn l_DoResultSBC_continue_elim(
    mut v_00_u03b1_4121_: *mut LeanObject,
    mut v_00_u03c3_4122_: *mut LeanObject,
    mut v_motive_4123_: *mut LeanObject,
    mut v_t_4124_: *mut LeanObject,
    mut v_h_4125_: *mut LeanObject,
    mut v_continue_4126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_DoResultSBC_ctorElim___redArg(v_t_4124_, v_continue_4126_);
    return v___x_4127_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1()
-> *mut LeanObject {
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    v___x_4148_ = l___aux__Init__Core______macroRules__term___u2248____1___closed__0;
    v___x_4149_ = l_String_toRawSubstring_x27(v___x_4148_);
    return v___x_4149_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2248____1(
    mut v_x_4161_: *mut LeanObject,
    mut v_a_4162_: *mut LeanObject,
    mut v_a_4163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: u8 = 0;
    v___x_4164_ = l_term___u2248___00__closed__1;
    lean_inc(v_x_4161_);
    v___x_4165_ = l_Lean_Syntax_isOfKind(v_x_4161_, v___x_4164_);
    if v___x_4165_ == 0 {
        let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4161_);
        v___x_4166_ = lean_box(1);
        v___x_4167_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4167_, 0, v___x_4166_);
        lean_ctor_set(v___x_4167_, 1, v_a_4163_);
        return v___x_4167_;
    } else {
        let mut v_quotContext_4168_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4169_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4175_: u8 = 0;
        let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4168_ = lean_ctor_get(v_a_4162_, 1);
        v_currMacroScope_4169_ = lean_ctor_get(v_a_4162_, 2);
        v_ref_4170_ = lean_ctor_get(v_a_4162_, 5);
        v___x_4171_ = lean_unsigned_to_nat(0);
        v___x_4172_ = l_Lean_Syntax_getArg(v_x_4161_, v___x_4171_);
        v___x_4173_ = lean_unsigned_to_nat(2);
        v___x_4174_ = l_Lean_Syntax_getArg(v_x_4161_, v___x_4173_);
        lean_dec(v_x_4161_);
        v___x_4175_ = 0;
        v___x_4176_ = l_Lean_SourceInfo_fromRef(v_ref_4170_, v___x_4175_);
        v___x_4177_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_4178_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2248____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2248____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1,
        );
        v___x_4179_ = l___aux__Init__Core______macroRules__term___u2248____1___closed__4;
        lean_inc(v_currMacroScope_4169_);
        lean_inc(v_quotContext_4168_);
        v___x_4180_ =
            l_Lean_addMacroScope(v_quotContext_4168_, v___x_4179_, v_currMacroScope_4169_);
        v___x_4181_ = l___aux__Init__Core______macroRules__term___u2248____1___closed__6;
        lean_inc_n(v___x_4176_, 2);
        v___x_4182_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4182_, 0, v___x_4176_);
        lean_ctor_set(v___x_4182_, 1, v___x_4178_);
        lean_ctor_set(v___x_4182_, 2, v___x_4180_);
        lean_ctor_set(v___x_4182_, 3, v___x_4181_);
        v___x_4183_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_4184_ = l_Lean_Syntax_node2(v___x_4176_, v___x_4183_, v___x_4172_, v___x_4174_);
        v___x_4185_ = l_Lean_Syntax_node2(v___x_4176_, v___x_4177_, v___x_4182_, v___x_4184_);
        v___x_4186_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4186_, 0, v___x_4185_);
        lean_ctor_set(v___x_4186_, 1, v_a_4163_);
        return v___x_4186_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2248____1___boxed(
    mut v_x_4187_: *mut LeanObject,
    mut v_a_4188_: *mut LeanObject,
    mut v_a_4189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4190_: *mut LeanObject = core::ptr::null_mut();
    v_res_4190_ =
        l___aux__Init__Core______macroRules__term___u2248____1(v_x_4187_, v_a_4188_, v_a_4189_);
    lean_dec_ref(v_a_4188_);
    return v_res_4190_;
}
pub unsafe fn l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(
    mut v_x_4191_: *mut LeanObject,
    mut v_a_4192_: *mut LeanObject,
    mut v_a_4193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: u8 = 0;
    v___x_4194_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_4191_);
    v___x_4195_ = l_Lean_Syntax_isOfKind(v_x_4191_, v___x_4194_);
    if v___x_4195_ == 0 {
        let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4191_);
        v___x_4196_ = lean_box(0);
        v___x_4197_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4197_, 0, v___x_4196_);
        lean_ctor_set(v___x_4197_, 1, v_a_4193_);
        return v___x_4197_;
    } else {
        let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4201_: u8 = 0;
        v___x_4198_ = lean_unsigned_to_nat(0);
        v___x_4199_ = l_Lean_Syntax_getArg(v_x_4191_, v___x_4198_);
        v___x_4200_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_4199_);
        v___x_4201_ = l_Lean_Syntax_isOfKind(v___x_4199_, v___x_4200_);
        if v___x_4201_ == 0 {
            let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4199_);
            lean_dec(v_x_4191_);
            v___x_4202_ = lean_box(0);
            v___x_4203_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_4203_, 0, v___x_4202_);
            lean_ctor_set(v___x_4203_, 1, v_a_4193_);
            return v___x_4203_;
        } else {
            let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4207_: u8 = 0;
            v___x_4204_ = lean_unsigned_to_nat(1);
            v___x_4205_ = l_Lean_Syntax_getArg(v_x_4191_, v___x_4204_);
            lean_dec(v_x_4191_);
            v___x_4206_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_4205_);
            v___x_4207_ = l_Lean_Syntax_matchesNull(v___x_4205_, v___x_4206_);
            if v___x_4207_ == 0 {
                let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4205_);
                lean_dec(v___x_4199_);
                v___x_4208_ = lean_box(0);
                v___x_4209_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4209_, 0, v___x_4208_);
                lean_ctor_set(v___x_4209_, 1, v_a_4193_);
                return v___x_4209_;
            } else {
                let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_4212_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4213_: u8 = 0;
                let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
                v___x_4210_ = l_Lean_Syntax_getArg(v___x_4205_, v___x_4198_);
                v___x_4211_ = l_Lean_Syntax_getArg(v___x_4205_, v___x_4204_);
                lean_dec(v___x_4205_);
                v_ref_4212_ = l_Lean_replaceRef(v___x_4199_, v_a_4192_);
                lean_dec(v___x_4199_);
                v___x_4213_ = 0;
                v___x_4214_ = l_Lean_SourceInfo_fromRef(v_ref_4212_, v___x_4213_);
                lean_dec(v_ref_4212_);
                v___x_4215_ = l_term___u2248___00__closed__1;
                v___x_4216_ = l_term___u2248___00__closed__2;
                lean_inc(v___x_4214_);
                v___x_4217_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4217_, 0, v___x_4214_);
                lean_ctor_set(v___x_4217_, 1, v___x_4216_);
                v___x_4218_ = l_Lean_Syntax_node3(
                    v___x_4214_,
                    v___x_4215_,
                    v___x_4210_,
                    v___x_4217_,
                    v___x_4211_,
                );
                v___x_4219_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4219_, 0, v___x_4218_);
                lean_ctor_set(v___x_4219_, 1, v_a_4193_);
                return v___x_4219_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__HasEquiv__Equiv__1___boxed(
    mut v_x_4220_: *mut LeanObject,
    mut v_a_4221_: *mut LeanObject,
    mut v_a_4222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4223_: *mut LeanObject = core::ptr::null_mut();
    v_res_4223_ =
        l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(v_x_4220_, v_a_4221_, v_a_4222_);
    lean_dec(v_a_4221_);
    return v_res_4223_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1()
-> *mut LeanObject {
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    v___x_4241_ = l___aux__Init__Core______macroRules__term___u2286____1___closed__0;
    v___x_4242_ = l_String_toRawSubstring_x27(v___x_4241_);
    return v___x_4242_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2286____1(
    mut v_x_4255_: *mut LeanObject,
    mut v_a_4256_: *mut LeanObject,
    mut v_a_4257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: u8 = 0;
    v___x_4258_ = l_term___u2286___00__closed__1;
    lean_inc(v_x_4255_);
    v___x_4259_ = l_Lean_Syntax_isOfKind(v_x_4255_, v___x_4258_);
    if v___x_4259_ == 0 {
        let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4255_);
        v___x_4260_ = lean_box(1);
        v___x_4261_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4261_, 0, v___x_4260_);
        lean_ctor_set(v___x_4261_, 1, v_a_4257_);
        return v___x_4261_;
    } else {
        let mut v_quotContext_4262_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4263_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4269_: u8 = 0;
        let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4262_ = lean_ctor_get(v_a_4256_, 1);
        v_currMacroScope_4263_ = lean_ctor_get(v_a_4256_, 2);
        v_ref_4264_ = lean_ctor_get(v_a_4256_, 5);
        v___x_4265_ = lean_unsigned_to_nat(0);
        v___x_4266_ = l_Lean_Syntax_getArg(v_x_4255_, v___x_4265_);
        v___x_4267_ = lean_unsigned_to_nat(2);
        v___x_4268_ = l_Lean_Syntax_getArg(v_x_4255_, v___x_4267_);
        lean_dec(v_x_4255_);
        v___x_4269_ = 0;
        v___x_4270_ = l_Lean_SourceInfo_fromRef(v_ref_4264_, v___x_4269_);
        v___x_4271_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_4272_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2286____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2286____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1,
        );
        v___x_4273_ = l___aux__Init__Core______macroRules__term___u2286____1___closed__2;
        lean_inc(v_currMacroScope_4263_);
        lean_inc(v_quotContext_4262_);
        v___x_4274_ =
            l_Lean_addMacroScope(v_quotContext_4262_, v___x_4273_, v_currMacroScope_4263_);
        v___x_4275_ = l___aux__Init__Core______macroRules__term___u2286____1___closed__6;
        lean_inc_n(v___x_4270_, 2);
        v___x_4276_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4276_, 0, v___x_4270_);
        lean_ctor_set(v___x_4276_, 1, v___x_4272_);
        lean_ctor_set(v___x_4276_, 2, v___x_4274_);
        lean_ctor_set(v___x_4276_, 3, v___x_4275_);
        v___x_4277_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_4278_ = l_Lean_Syntax_node2(v___x_4270_, v___x_4277_, v___x_4266_, v___x_4268_);
        v___x_4279_ = l_Lean_Syntax_node2(v___x_4270_, v___x_4271_, v___x_4276_, v___x_4278_);
        v___x_4280_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4280_, 0, v___x_4279_);
        lean_ctor_set(v___x_4280_, 1, v_a_4257_);
        return v___x_4280_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2286____1___boxed(
    mut v_x_4281_: *mut LeanObject,
    mut v_a_4282_: *mut LeanObject,
    mut v_a_4283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4284_: *mut LeanObject = core::ptr::null_mut();
    v_res_4284_ =
        l___aux__Init__Core______macroRules__term___u2286____1(v_x_4281_, v_a_4282_, v_a_4283_);
    lean_dec_ref(v_a_4282_);
    return v_res_4284_;
}
pub unsafe fn l___aux__Init__Core______unexpand__HasSubset__Subset__1(
    mut v_x_4285_: *mut LeanObject,
    mut v_a_4286_: *mut LeanObject,
    mut v_a_4287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: u8 = 0;
    v___x_4288_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_4285_);
    v___x_4289_ = l_Lean_Syntax_isOfKind(v_x_4285_, v___x_4288_);
    if v___x_4289_ == 0 {
        let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4285_);
        v___x_4290_ = lean_box(0);
        v___x_4291_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4291_, 0, v___x_4290_);
        lean_ctor_set(v___x_4291_, 1, v_a_4287_);
        return v___x_4291_;
    } else {
        let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4295_: u8 = 0;
        v___x_4292_ = lean_unsigned_to_nat(0);
        v___x_4293_ = l_Lean_Syntax_getArg(v_x_4285_, v___x_4292_);
        v___x_4294_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_4293_);
        v___x_4295_ = l_Lean_Syntax_isOfKind(v___x_4293_, v___x_4294_);
        if v___x_4295_ == 0 {
            let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4293_);
            lean_dec(v_x_4285_);
            v___x_4296_ = lean_box(0);
            v___x_4297_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_4297_, 0, v___x_4296_);
            lean_ctor_set(v___x_4297_, 1, v_a_4287_);
            return v___x_4297_;
        } else {
            let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4301_: u8 = 0;
            v___x_4298_ = lean_unsigned_to_nat(1);
            v___x_4299_ = l_Lean_Syntax_getArg(v_x_4285_, v___x_4298_);
            lean_dec(v_x_4285_);
            v___x_4300_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_4299_);
            v___x_4301_ = l_Lean_Syntax_matchesNull(v___x_4299_, v___x_4300_);
            if v___x_4301_ == 0 {
                let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4299_);
                lean_dec(v___x_4293_);
                v___x_4302_ = lean_box(0);
                v___x_4303_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4303_, 0, v___x_4302_);
                lean_ctor_set(v___x_4303_, 1, v_a_4287_);
                return v___x_4303_;
            } else {
                let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_4306_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4307_: u8 = 0;
                let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
                v___x_4304_ = l_Lean_Syntax_getArg(v___x_4299_, v___x_4292_);
                v___x_4305_ = l_Lean_Syntax_getArg(v___x_4299_, v___x_4298_);
                lean_dec(v___x_4299_);
                v_ref_4306_ = l_Lean_replaceRef(v___x_4293_, v_a_4286_);
                lean_dec(v___x_4293_);
                v___x_4307_ = 0;
                v___x_4308_ = l_Lean_SourceInfo_fromRef(v_ref_4306_, v___x_4307_);
                lean_dec(v_ref_4306_);
                v___x_4309_ = l_term___u2286___00__closed__1;
                v___x_4310_ = l_term___u2286___00__closed__2;
                lean_inc(v___x_4308_);
                v___x_4311_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4311_, 0, v___x_4308_);
                lean_ctor_set(v___x_4311_, 1, v___x_4310_);
                v___x_4312_ = l_Lean_Syntax_node3(
                    v___x_4308_,
                    v___x_4309_,
                    v___x_4304_,
                    v___x_4311_,
                    v___x_4305_,
                );
                v___x_4313_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4313_, 0, v___x_4312_);
                lean_ctor_set(v___x_4313_, 1, v_a_4287_);
                return v___x_4313_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__HasSubset__Subset__1___boxed(
    mut v_x_4314_: *mut LeanObject,
    mut v_a_4315_: *mut LeanObject,
    mut v_a_4316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4317_: *mut LeanObject = core::ptr::null_mut();
    v_res_4317_ =
        l___aux__Init__Core______unexpand__HasSubset__Subset__1(v_x_4314_, v_a_4315_, v_a_4316_);
    lean_dec(v_a_4315_);
    return v_res_4317_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1()
-> *mut LeanObject {
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    v___x_4335_ = l___aux__Init__Core______macroRules__term___u2282____1___closed__0;
    v___x_4336_ = l_String_toRawSubstring_x27(v___x_4335_);
    return v___x_4336_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2282____1(
    mut v_x_4349_: *mut LeanObject,
    mut v_a_4350_: *mut LeanObject,
    mut v_a_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: u8 = 0;
    v___x_4352_ = l_term___u2282___00__closed__1;
    lean_inc(v_x_4349_);
    v___x_4353_ = l_Lean_Syntax_isOfKind(v_x_4349_, v___x_4352_);
    if v___x_4353_ == 0 {
        let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4349_);
        v___x_4354_ = lean_box(1);
        v___x_4355_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4355_, 0, v___x_4354_);
        lean_ctor_set(v___x_4355_, 1, v_a_4351_);
        return v___x_4355_;
    } else {
        let mut v_quotContext_4356_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4357_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4363_: u8 = 0;
        let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4356_ = lean_ctor_get(v_a_4350_, 1);
        v_currMacroScope_4357_ = lean_ctor_get(v_a_4350_, 2);
        v_ref_4358_ = lean_ctor_get(v_a_4350_, 5);
        v___x_4359_ = lean_unsigned_to_nat(0);
        v___x_4360_ = l_Lean_Syntax_getArg(v_x_4349_, v___x_4359_);
        v___x_4361_ = lean_unsigned_to_nat(2);
        v___x_4362_ = l_Lean_Syntax_getArg(v_x_4349_, v___x_4361_);
        lean_dec(v_x_4349_);
        v___x_4363_ = 0;
        v___x_4364_ = l_Lean_SourceInfo_fromRef(v_ref_4358_, v___x_4363_);
        v___x_4365_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_4366_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2282____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2282____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1,
        );
        v___x_4367_ = l___aux__Init__Core______macroRules__term___u2282____1___closed__2;
        lean_inc(v_currMacroScope_4357_);
        lean_inc(v_quotContext_4356_);
        v___x_4368_ =
            l_Lean_addMacroScope(v_quotContext_4356_, v___x_4367_, v_currMacroScope_4357_);
        v___x_4369_ = l___aux__Init__Core______macroRules__term___u2282____1___closed__6;
        lean_inc_n(v___x_4364_, 2);
        v___x_4370_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4370_, 0, v___x_4364_);
        lean_ctor_set(v___x_4370_, 1, v___x_4366_);
        lean_ctor_set(v___x_4370_, 2, v___x_4368_);
        lean_ctor_set(v___x_4370_, 3, v___x_4369_);
        v___x_4371_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_4372_ = l_Lean_Syntax_node2(v___x_4364_, v___x_4371_, v___x_4360_, v___x_4362_);
        v___x_4373_ = l_Lean_Syntax_node2(v___x_4364_, v___x_4365_, v___x_4370_, v___x_4372_);
        v___x_4374_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4374_, 0, v___x_4373_);
        lean_ctor_set(v___x_4374_, 1, v_a_4351_);
        return v___x_4374_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2282____1___boxed(
    mut v_x_4375_: *mut LeanObject,
    mut v_a_4376_: *mut LeanObject,
    mut v_a_4377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4378_: *mut LeanObject = core::ptr::null_mut();
    v_res_4378_ =
        l___aux__Init__Core______macroRules__term___u2282____1(v_x_4375_, v_a_4376_, v_a_4377_);
    lean_dec_ref(v_a_4376_);
    return v_res_4378_;
}
pub unsafe fn l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(
    mut v_x_4379_: *mut LeanObject,
    mut v_a_4380_: *mut LeanObject,
    mut v_a_4381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    v___x_4382_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_4379_);
    v___x_4383_ = l_Lean_Syntax_isOfKind(v_x_4379_, v___x_4382_);
    if v___x_4383_ == 0 {
        let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4379_);
        v___x_4384_ = lean_box(0);
        v___x_4385_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4385_, 0, v___x_4384_);
        lean_ctor_set(v___x_4385_, 1, v_a_4381_);
        return v___x_4385_;
    } else {
        let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4389_: u8 = 0;
        v___x_4386_ = lean_unsigned_to_nat(0);
        v___x_4387_ = l_Lean_Syntax_getArg(v_x_4379_, v___x_4386_);
        v___x_4388_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_4387_);
        v___x_4389_ = l_Lean_Syntax_isOfKind(v___x_4387_, v___x_4388_);
        if v___x_4389_ == 0 {
            let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4387_);
            lean_dec(v_x_4379_);
            v___x_4390_ = lean_box(0);
            v___x_4391_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_4391_, 0, v___x_4390_);
            lean_ctor_set(v___x_4391_, 1, v_a_4381_);
            return v___x_4391_;
        } else {
            let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4395_: u8 = 0;
            v___x_4392_ = lean_unsigned_to_nat(1);
            v___x_4393_ = l_Lean_Syntax_getArg(v_x_4379_, v___x_4392_);
            lean_dec(v_x_4379_);
            v___x_4394_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_4393_);
            v___x_4395_ = l_Lean_Syntax_matchesNull(v___x_4393_, v___x_4394_);
            if v___x_4395_ == 0 {
                let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4393_);
                lean_dec(v___x_4387_);
                v___x_4396_ = lean_box(0);
                v___x_4397_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4397_, 0, v___x_4396_);
                lean_ctor_set(v___x_4397_, 1, v_a_4381_);
                return v___x_4397_;
            } else {
                let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_4400_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4401_: u8 = 0;
                let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
                v___x_4398_ = l_Lean_Syntax_getArg(v___x_4393_, v___x_4386_);
                v___x_4399_ = l_Lean_Syntax_getArg(v___x_4393_, v___x_4392_);
                lean_dec(v___x_4393_);
                v_ref_4400_ = l_Lean_replaceRef(v___x_4387_, v_a_4380_);
                lean_dec(v___x_4387_);
                v___x_4401_ = 0;
                v___x_4402_ = l_Lean_SourceInfo_fromRef(v_ref_4400_, v___x_4401_);
                lean_dec(v_ref_4400_);
                v___x_4403_ = l_term___u2282___00__closed__1;
                v___x_4404_ = l_term___u2282___00__closed__2;
                lean_inc(v___x_4402_);
                v___x_4405_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4405_, 0, v___x_4402_);
                lean_ctor_set(v___x_4405_, 1, v___x_4404_);
                v___x_4406_ = l_Lean_Syntax_node3(
                    v___x_4402_,
                    v___x_4403_,
                    v___x_4398_,
                    v___x_4405_,
                    v___x_4399_,
                );
                v___x_4407_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4407_, 0, v___x_4406_);
                lean_ctor_set(v___x_4407_, 1, v_a_4381_);
                return v___x_4407_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__HasSSubset__SSubset__1___boxed(
    mut v_x_4408_: *mut LeanObject,
    mut v_a_4409_: *mut LeanObject,
    mut v_a_4410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4411_: *mut LeanObject = core::ptr::null_mut();
    v_res_4411_ =
        l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(v_x_4408_, v_a_4409_, v_a_4410_);
    lean_dec(v_a_4409_);
    return v_res_4411_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1()
-> *mut LeanObject {
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    v___x_4429_ = l___aux__Init__Core______macroRules__term___u2287____1___closed__0;
    v___x_4430_ = l_String_toRawSubstring_x27(v___x_4429_);
    return v___x_4430_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2287____1(
    mut v_x_4439_: *mut LeanObject,
    mut v_a_4440_: *mut LeanObject,
    mut v_a_4441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: u8 = 0;
    v___x_4442_ = l_term___u2287___00__closed__1;
    lean_inc(v_x_4439_);
    v___x_4443_ = l_Lean_Syntax_isOfKind(v_x_4439_, v___x_4442_);
    if v___x_4443_ == 0 {
        let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4439_);
        v___x_4444_ = lean_box(1);
        v___x_4445_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4445_, 0, v___x_4444_);
        lean_ctor_set(v___x_4445_, 1, v_a_4441_);
        return v___x_4445_;
    } else {
        let mut v_quotContext_4446_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4447_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4448_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4453_: u8 = 0;
        let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4446_ = lean_ctor_get(v_a_4440_, 1);
        v_currMacroScope_4447_ = lean_ctor_get(v_a_4440_, 2);
        v_ref_4448_ = lean_ctor_get(v_a_4440_, 5);
        v___x_4449_ = lean_unsigned_to_nat(0);
        v___x_4450_ = l_Lean_Syntax_getArg(v_x_4439_, v___x_4449_);
        v___x_4451_ = lean_unsigned_to_nat(2);
        v___x_4452_ = l_Lean_Syntax_getArg(v_x_4439_, v___x_4451_);
        lean_dec(v_x_4439_);
        v___x_4453_ = 0;
        v___x_4454_ = l_Lean_SourceInfo_fromRef(v_ref_4448_, v___x_4453_);
        v___x_4455_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_4456_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2287____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2287____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1,
        );
        v___x_4457_ = l___aux__Init__Core______macroRules__term___u2287____1___closed__2;
        lean_inc(v_currMacroScope_4447_);
        lean_inc(v_quotContext_4446_);
        v___x_4458_ =
            l_Lean_addMacroScope(v_quotContext_4446_, v___x_4457_, v_currMacroScope_4447_);
        v___x_4459_ = l___aux__Init__Core______macroRules__term___u2287____1___closed__4;
        lean_inc_n(v___x_4454_, 2);
        v___x_4460_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4460_, 0, v___x_4454_);
        lean_ctor_set(v___x_4460_, 1, v___x_4456_);
        lean_ctor_set(v___x_4460_, 2, v___x_4458_);
        lean_ctor_set(v___x_4460_, 3, v___x_4459_);
        v___x_4461_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_4462_ = l_Lean_Syntax_node2(v___x_4454_, v___x_4461_, v___x_4450_, v___x_4452_);
        v___x_4463_ = l_Lean_Syntax_node2(v___x_4454_, v___x_4455_, v___x_4460_, v___x_4462_);
        v___x_4464_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4464_, 0, v___x_4463_);
        lean_ctor_set(v___x_4464_, 1, v_a_4441_);
        return v___x_4464_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2287____1___boxed(
    mut v_x_4465_: *mut LeanObject,
    mut v_a_4466_: *mut LeanObject,
    mut v_a_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4468_: *mut LeanObject = core::ptr::null_mut();
    v_res_4468_ =
        l___aux__Init__Core______macroRules__term___u2287____1(v_x_4465_, v_a_4466_, v_a_4467_);
    lean_dec_ref(v_a_4466_);
    return v_res_4468_;
}
pub unsafe fn l___aux__Init__Core______unexpand__Superset__1(
    mut v_x_4469_: *mut LeanObject,
    mut v_a_4470_: *mut LeanObject,
    mut v_a_4471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: u8 = 0;
    v___x_4472_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_4469_);
    v___x_4473_ = l_Lean_Syntax_isOfKind(v_x_4469_, v___x_4472_);
    if v___x_4473_ == 0 {
        let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4469_);
        v___x_4474_ = lean_box(0);
        v___x_4475_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4475_, 0, v___x_4474_);
        lean_ctor_set(v___x_4475_, 1, v_a_4471_);
        return v___x_4475_;
    } else {
        let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4479_: u8 = 0;
        v___x_4476_ = lean_unsigned_to_nat(0);
        v___x_4477_ = l_Lean_Syntax_getArg(v_x_4469_, v___x_4476_);
        v___x_4478_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_4477_);
        v___x_4479_ = l_Lean_Syntax_isOfKind(v___x_4477_, v___x_4478_);
        if v___x_4479_ == 0 {
            let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4477_);
            lean_dec(v_x_4469_);
            v___x_4480_ = lean_box(0);
            v___x_4481_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_4481_, 0, v___x_4480_);
            lean_ctor_set(v___x_4481_, 1, v_a_4471_);
            return v___x_4481_;
        } else {
            let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4485_: u8 = 0;
            v___x_4482_ = lean_unsigned_to_nat(1);
            v___x_4483_ = l_Lean_Syntax_getArg(v_x_4469_, v___x_4482_);
            lean_dec(v_x_4469_);
            v___x_4484_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_4483_);
            v___x_4485_ = l_Lean_Syntax_matchesNull(v___x_4483_, v___x_4484_);
            if v___x_4485_ == 0 {
                let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4483_);
                lean_dec(v___x_4477_);
                v___x_4486_ = lean_box(0);
                v___x_4487_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4487_, 0, v___x_4486_);
                lean_ctor_set(v___x_4487_, 1, v_a_4471_);
                return v___x_4487_;
            } else {
                let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_4490_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4491_: u8 = 0;
                let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
                v___x_4488_ = l_Lean_Syntax_getArg(v___x_4483_, v___x_4476_);
                v___x_4489_ = l_Lean_Syntax_getArg(v___x_4483_, v___x_4482_);
                lean_dec(v___x_4483_);
                v_ref_4490_ = l_Lean_replaceRef(v___x_4477_, v_a_4470_);
                lean_dec(v___x_4477_);
                v___x_4491_ = 0;
                v___x_4492_ = l_Lean_SourceInfo_fromRef(v_ref_4490_, v___x_4491_);
                lean_dec(v_ref_4490_);
                v___x_4493_ = l_term___u2287___00__closed__1;
                v___x_4494_ = l_term___u2287___00__closed__2;
                lean_inc(v___x_4492_);
                v___x_4495_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4495_, 0, v___x_4492_);
                lean_ctor_set(v___x_4495_, 1, v___x_4494_);
                v___x_4496_ = l_Lean_Syntax_node3(
                    v___x_4492_,
                    v___x_4493_,
                    v___x_4488_,
                    v___x_4495_,
                    v___x_4489_,
                );
                v___x_4497_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4497_, 0, v___x_4496_);
                lean_ctor_set(v___x_4497_, 1, v_a_4471_);
                return v___x_4497_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__Superset__1___boxed(
    mut v_x_4498_: *mut LeanObject,
    mut v_a_4499_: *mut LeanObject,
    mut v_a_4500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4501_: *mut LeanObject = core::ptr::null_mut();
    v_res_4501_ = l___aux__Init__Core______unexpand__Superset__1(v_x_4498_, v_a_4499_, v_a_4500_);
    lean_dec(v_a_4499_);
    return v_res_4501_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1()
-> *mut LeanObject {
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    v___x_4519_ = l___aux__Init__Core______macroRules__term___u2283____1___closed__0;
    v___x_4520_ = l_String_toRawSubstring_x27(v___x_4519_);
    return v___x_4520_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2283____1(
    mut v_x_4529_: *mut LeanObject,
    mut v_a_4530_: *mut LeanObject,
    mut v_a_4531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: u8 = 0;
    v___x_4532_ = l_term___u2283___00__closed__1;
    lean_inc(v_x_4529_);
    v___x_4533_ = l_Lean_Syntax_isOfKind(v_x_4529_, v___x_4532_);
    if v___x_4533_ == 0 {
        let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4529_);
        v___x_4534_ = lean_box(1);
        v___x_4535_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4535_, 0, v___x_4534_);
        lean_ctor_set(v___x_4535_, 1, v_a_4531_);
        return v___x_4535_;
    } else {
        let mut v_quotContext_4536_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4537_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4543_: u8 = 0;
        let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4536_ = lean_ctor_get(v_a_4530_, 1);
        v_currMacroScope_4537_ = lean_ctor_get(v_a_4530_, 2);
        v_ref_4538_ = lean_ctor_get(v_a_4530_, 5);
        v___x_4539_ = lean_unsigned_to_nat(0);
        v___x_4540_ = l_Lean_Syntax_getArg(v_x_4529_, v___x_4539_);
        v___x_4541_ = lean_unsigned_to_nat(2);
        v___x_4542_ = l_Lean_Syntax_getArg(v_x_4529_, v___x_4541_);
        lean_dec(v_x_4529_);
        v___x_4543_ = 0;
        v___x_4544_ = l_Lean_SourceInfo_fromRef(v_ref_4538_, v___x_4543_);
        v___x_4545_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_4546_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2283____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2283____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1,
        );
        v___x_4547_ = l___aux__Init__Core______macroRules__term___u2283____1___closed__2;
        lean_inc(v_currMacroScope_4537_);
        lean_inc(v_quotContext_4536_);
        v___x_4548_ =
            l_Lean_addMacroScope(v_quotContext_4536_, v___x_4547_, v_currMacroScope_4537_);
        v___x_4549_ = l___aux__Init__Core______macroRules__term___u2283____1___closed__4;
        lean_inc_n(v___x_4544_, 2);
        v___x_4550_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4550_, 0, v___x_4544_);
        lean_ctor_set(v___x_4550_, 1, v___x_4546_);
        lean_ctor_set(v___x_4550_, 2, v___x_4548_);
        lean_ctor_set(v___x_4550_, 3, v___x_4549_);
        v___x_4551_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_4552_ = l_Lean_Syntax_node2(v___x_4544_, v___x_4551_, v___x_4540_, v___x_4542_);
        v___x_4553_ = l_Lean_Syntax_node2(v___x_4544_, v___x_4545_, v___x_4550_, v___x_4552_);
        v___x_4554_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4554_, 0, v___x_4553_);
        lean_ctor_set(v___x_4554_, 1, v_a_4531_);
        return v___x_4554_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2283____1___boxed(
    mut v_x_4555_: *mut LeanObject,
    mut v_a_4556_: *mut LeanObject,
    mut v_a_4557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4558_: *mut LeanObject = core::ptr::null_mut();
    v_res_4558_ =
        l___aux__Init__Core______macroRules__term___u2283____1(v_x_4555_, v_a_4556_, v_a_4557_);
    lean_dec_ref(v_a_4556_);
    return v_res_4558_;
}
pub unsafe fn l___aux__Init__Core______unexpand__SSuperset__1(
    mut v_x_4559_: *mut LeanObject,
    mut v_a_4560_: *mut LeanObject,
    mut v_a_4561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: u8 = 0;
    v___x_4562_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_4559_);
    v___x_4563_ = l_Lean_Syntax_isOfKind(v_x_4559_, v___x_4562_);
    if v___x_4563_ == 0 {
        let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4559_);
        v___x_4564_ = lean_box(0);
        v___x_4565_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4565_, 0, v___x_4564_);
        lean_ctor_set(v___x_4565_, 1, v_a_4561_);
        return v___x_4565_;
    } else {
        let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4569_: u8 = 0;
        v___x_4566_ = lean_unsigned_to_nat(0);
        v___x_4567_ = l_Lean_Syntax_getArg(v_x_4559_, v___x_4566_);
        v___x_4568_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_4567_);
        v___x_4569_ = l_Lean_Syntax_isOfKind(v___x_4567_, v___x_4568_);
        if v___x_4569_ == 0 {
            let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4567_);
            lean_dec(v_x_4559_);
            v___x_4570_ = lean_box(0);
            v___x_4571_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_4571_, 0, v___x_4570_);
            lean_ctor_set(v___x_4571_, 1, v_a_4561_);
            return v___x_4571_;
        } else {
            let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4575_: u8 = 0;
            v___x_4572_ = lean_unsigned_to_nat(1);
            v___x_4573_ = l_Lean_Syntax_getArg(v_x_4559_, v___x_4572_);
            lean_dec(v_x_4559_);
            v___x_4574_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_4573_);
            v___x_4575_ = l_Lean_Syntax_matchesNull(v___x_4573_, v___x_4574_);
            if v___x_4575_ == 0 {
                let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4573_);
                lean_dec(v___x_4567_);
                v___x_4576_ = lean_box(0);
                v___x_4577_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4577_, 0, v___x_4576_);
                lean_ctor_set(v___x_4577_, 1, v_a_4561_);
                return v___x_4577_;
            } else {
                let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_4580_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4581_: u8 = 0;
                let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
                v___x_4578_ = l_Lean_Syntax_getArg(v___x_4573_, v___x_4566_);
                v___x_4579_ = l_Lean_Syntax_getArg(v___x_4573_, v___x_4572_);
                lean_dec(v___x_4573_);
                v_ref_4580_ = l_Lean_replaceRef(v___x_4567_, v_a_4560_);
                lean_dec(v___x_4567_);
                v___x_4581_ = 0;
                v___x_4582_ = l_Lean_SourceInfo_fromRef(v_ref_4580_, v___x_4581_);
                lean_dec(v_ref_4580_);
                v___x_4583_ = l_term___u2283___00__closed__1;
                v___x_4584_ = l_term___u2283___00__closed__2;
                lean_inc(v___x_4582_);
                v___x_4585_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4585_, 0, v___x_4582_);
                lean_ctor_set(v___x_4585_, 1, v___x_4584_);
                v___x_4586_ = l_Lean_Syntax_node3(
                    v___x_4582_,
                    v___x_4583_,
                    v___x_4578_,
                    v___x_4585_,
                    v___x_4579_,
                );
                v___x_4587_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4587_, 0, v___x_4586_);
                lean_ctor_set(v___x_4587_, 1, v_a_4561_);
                return v___x_4587_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__SSuperset__1___boxed(
    mut v_x_4588_: *mut LeanObject,
    mut v_a_4589_: *mut LeanObject,
    mut v_a_4590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4591_: *mut LeanObject = core::ptr::null_mut();
    v_res_4591_ = l___aux__Init__Core______unexpand__SSuperset__1(v_x_4588_, v_a_4589_, v_a_4590_);
    lean_dec(v_a_4589_);
    return v_res_4591_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1()
-> *mut LeanObject {
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    v___x_4611_ = l___aux__Init__Core______macroRules__term___u222a____1___closed__0;
    v___x_4612_ = l_String_toRawSubstring_x27(v___x_4611_);
    return v___x_4612_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u222a____1(
    mut v_x_4624_: *mut LeanObject,
    mut v_a_4625_: *mut LeanObject,
    mut v_a_4626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: u8 = 0;
    v___x_4627_ = l_term___u222a___00__closed__1;
    lean_inc(v_x_4624_);
    v___x_4628_ = l_Lean_Syntax_isOfKind(v_x_4624_, v___x_4627_);
    if v___x_4628_ == 0 {
        let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4624_);
        v___x_4629_ = lean_box(1);
        v___x_4630_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4630_, 0, v___x_4629_);
        lean_ctor_set(v___x_4630_, 1, v_a_4626_);
        return v___x_4630_;
    } else {
        let mut v_quotContext_4631_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4632_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4638_: u8 = 0;
        let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4631_ = lean_ctor_get(v_a_4625_, 1);
        v_currMacroScope_4632_ = lean_ctor_get(v_a_4625_, 2);
        v_ref_4633_ = lean_ctor_get(v_a_4625_, 5);
        v___x_4634_ = lean_unsigned_to_nat(0);
        v___x_4635_ = l_Lean_Syntax_getArg(v_x_4624_, v___x_4634_);
        v___x_4636_ = lean_unsigned_to_nat(2);
        v___x_4637_ = l_Lean_Syntax_getArg(v_x_4624_, v___x_4636_);
        lean_dec(v_x_4624_);
        v___x_4638_ = 0;
        v___x_4639_ = l_Lean_SourceInfo_fromRef(v_ref_4633_, v___x_4638_);
        v___x_4640_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_4641_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u222a____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u222a____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1,
        );
        v___x_4642_ = l___aux__Init__Core______macroRules__term___u222a____1___closed__4;
        lean_inc(v_currMacroScope_4632_);
        lean_inc(v_quotContext_4631_);
        v___x_4643_ =
            l_Lean_addMacroScope(v_quotContext_4631_, v___x_4642_, v_currMacroScope_4632_);
        v___x_4644_ = l___aux__Init__Core______macroRules__term___u222a____1___closed__6;
        lean_inc_n(v___x_4639_, 2);
        v___x_4645_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4645_, 0, v___x_4639_);
        lean_ctor_set(v___x_4645_, 1, v___x_4641_);
        lean_ctor_set(v___x_4645_, 2, v___x_4643_);
        lean_ctor_set(v___x_4645_, 3, v___x_4644_);
        v___x_4646_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_4647_ = l_Lean_Syntax_node2(v___x_4639_, v___x_4646_, v___x_4635_, v___x_4637_);
        v___x_4648_ = l_Lean_Syntax_node2(v___x_4639_, v___x_4640_, v___x_4645_, v___x_4647_);
        v___x_4649_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4649_, 0, v___x_4648_);
        lean_ctor_set(v___x_4649_, 1, v_a_4626_);
        return v___x_4649_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u222a____1___boxed(
    mut v_x_4650_: *mut LeanObject,
    mut v_a_4651_: *mut LeanObject,
    mut v_a_4652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4653_: *mut LeanObject = core::ptr::null_mut();
    v_res_4653_ =
        l___aux__Init__Core______macroRules__term___u222a____1(v_x_4650_, v_a_4651_, v_a_4652_);
    lean_dec_ref(v_a_4651_);
    return v_res_4653_;
}
pub unsafe fn l___aux__Init__Core______unexpand__Union__union__1(
    mut v_x_4654_: *mut LeanObject,
    mut v_a_4655_: *mut LeanObject,
    mut v_a_4656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: u8 = 0;
    v___x_4657_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_4654_);
    v___x_4658_ = l_Lean_Syntax_isOfKind(v_x_4654_, v___x_4657_);
    if v___x_4658_ == 0 {
        let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4654_);
        v___x_4659_ = lean_box(0);
        v___x_4660_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4660_, 0, v___x_4659_);
        lean_ctor_set(v___x_4660_, 1, v_a_4656_);
        return v___x_4660_;
    } else {
        let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4664_: u8 = 0;
        v___x_4661_ = lean_unsigned_to_nat(0);
        v___x_4662_ = l_Lean_Syntax_getArg(v_x_4654_, v___x_4661_);
        v___x_4663_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_4662_);
        v___x_4664_ = l_Lean_Syntax_isOfKind(v___x_4662_, v___x_4663_);
        if v___x_4664_ == 0 {
            let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4662_);
            lean_dec(v_x_4654_);
            v___x_4665_ = lean_box(0);
            v___x_4666_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_4666_, 0, v___x_4665_);
            lean_ctor_set(v___x_4666_, 1, v_a_4656_);
            return v___x_4666_;
        } else {
            let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4670_: u8 = 0;
            v___x_4667_ = lean_unsigned_to_nat(1);
            v___x_4668_ = l_Lean_Syntax_getArg(v_x_4654_, v___x_4667_);
            lean_dec(v_x_4654_);
            v___x_4669_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_4668_);
            v___x_4670_ = l_Lean_Syntax_matchesNull(v___x_4668_, v___x_4669_);
            if v___x_4670_ == 0 {
                let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4668_);
                lean_dec(v___x_4662_);
                v___x_4671_ = lean_box(0);
                v___x_4672_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4672_, 0, v___x_4671_);
                lean_ctor_set(v___x_4672_, 1, v_a_4656_);
                return v___x_4672_;
            } else {
                let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_4675_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4676_: u8 = 0;
                let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
                v___x_4673_ = l_Lean_Syntax_getArg(v___x_4668_, v___x_4661_);
                v___x_4674_ = l_Lean_Syntax_getArg(v___x_4668_, v___x_4667_);
                lean_dec(v___x_4668_);
                v_ref_4675_ = l_Lean_replaceRef(v___x_4662_, v_a_4655_);
                lean_dec(v___x_4662_);
                v___x_4676_ = 0;
                v___x_4677_ = l_Lean_SourceInfo_fromRef(v_ref_4675_, v___x_4676_);
                lean_dec(v_ref_4675_);
                v___x_4678_ = l_term___u222a___00__closed__1;
                v___x_4679_ = l_term___u222a___00__closed__2;
                lean_inc(v___x_4677_);
                v___x_4680_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4680_, 0, v___x_4677_);
                lean_ctor_set(v___x_4680_, 1, v___x_4679_);
                v___x_4681_ = l_Lean_Syntax_node3(
                    v___x_4677_,
                    v___x_4678_,
                    v___x_4673_,
                    v___x_4680_,
                    v___x_4674_,
                );
                v___x_4682_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4682_, 0, v___x_4681_);
                lean_ctor_set(v___x_4682_, 1, v_a_4656_);
                return v___x_4682_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__Union__union__1___boxed(
    mut v_x_4683_: *mut LeanObject,
    mut v_a_4684_: *mut LeanObject,
    mut v_a_4685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4686_: *mut LeanObject = core::ptr::null_mut();
    v_res_4686_ =
        l___aux__Init__Core______unexpand__Union__union__1(v_x_4683_, v_a_4684_, v_a_4685_);
    lean_dec(v_a_4684_);
    return v_res_4686_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1()
-> *mut LeanObject {
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    v___x_4706_ = l___aux__Init__Core______macroRules__term___u2229____1___closed__0;
    v___x_4707_ = l_String_toRawSubstring_x27(v___x_4706_);
    return v___x_4707_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2229____1(
    mut v_x_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
    mut v_a_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: u8 = 0;
    v___x_4722_ = l_term___u2229___00__closed__1;
    lean_inc(v_x_4719_);
    v___x_4723_ = l_Lean_Syntax_isOfKind(v_x_4719_, v___x_4722_);
    if v___x_4723_ == 0 {
        let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4719_);
        v___x_4724_ = lean_box(1);
        v___x_4725_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4725_, 0, v___x_4724_);
        lean_ctor_set(v___x_4725_, 1, v_a_4721_);
        return v___x_4725_;
    } else {
        let mut v_quotContext_4726_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4727_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4728_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4733_: u8 = 0;
        let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4726_ = lean_ctor_get(v_a_4720_, 1);
        v_currMacroScope_4727_ = lean_ctor_get(v_a_4720_, 2);
        v_ref_4728_ = lean_ctor_get(v_a_4720_, 5);
        v___x_4729_ = lean_unsigned_to_nat(0);
        v___x_4730_ = l_Lean_Syntax_getArg(v_x_4719_, v___x_4729_);
        v___x_4731_ = lean_unsigned_to_nat(2);
        v___x_4732_ = l_Lean_Syntax_getArg(v_x_4719_, v___x_4731_);
        lean_dec(v_x_4719_);
        v___x_4733_ = 0;
        v___x_4734_ = l_Lean_SourceInfo_fromRef(v_ref_4728_, v___x_4733_);
        v___x_4735_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_4736_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2229____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2229____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1,
        );
        v___x_4737_ = l___aux__Init__Core______macroRules__term___u2229____1___closed__4;
        lean_inc(v_currMacroScope_4727_);
        lean_inc(v_quotContext_4726_);
        v___x_4738_ =
            l_Lean_addMacroScope(v_quotContext_4726_, v___x_4737_, v_currMacroScope_4727_);
        v___x_4739_ = l___aux__Init__Core______macroRules__term___u2229____1___closed__6;
        lean_inc_n(v___x_4734_, 2);
        v___x_4740_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4740_, 0, v___x_4734_);
        lean_ctor_set(v___x_4740_, 1, v___x_4736_);
        lean_ctor_set(v___x_4740_, 2, v___x_4738_);
        lean_ctor_set(v___x_4740_, 3, v___x_4739_);
        v___x_4741_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_4742_ = l_Lean_Syntax_node2(v___x_4734_, v___x_4741_, v___x_4730_, v___x_4732_);
        v___x_4743_ = l_Lean_Syntax_node2(v___x_4734_, v___x_4735_, v___x_4740_, v___x_4742_);
        v___x_4744_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4744_, 0, v___x_4743_);
        lean_ctor_set(v___x_4744_, 1, v_a_4721_);
        return v___x_4744_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2229____1___boxed(
    mut v_x_4745_: *mut LeanObject,
    mut v_a_4746_: *mut LeanObject,
    mut v_a_4747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4748_: *mut LeanObject = core::ptr::null_mut();
    v_res_4748_ =
        l___aux__Init__Core______macroRules__term___u2229____1(v_x_4745_, v_a_4746_, v_a_4747_);
    lean_dec_ref(v_a_4746_);
    return v_res_4748_;
}
pub unsafe fn l___aux__Init__Core______unexpand__Inter__inter__1(
    mut v_x_4749_: *mut LeanObject,
    mut v_a_4750_: *mut LeanObject,
    mut v_a_4751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: u8 = 0;
    v___x_4752_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_4749_);
    v___x_4753_ = l_Lean_Syntax_isOfKind(v_x_4749_, v___x_4752_);
    if v___x_4753_ == 0 {
        let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4749_);
        v___x_4754_ = lean_box(0);
        v___x_4755_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4755_, 0, v___x_4754_);
        lean_ctor_set(v___x_4755_, 1, v_a_4751_);
        return v___x_4755_;
    } else {
        let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4759_: u8 = 0;
        v___x_4756_ = lean_unsigned_to_nat(0);
        v___x_4757_ = l_Lean_Syntax_getArg(v_x_4749_, v___x_4756_);
        v___x_4758_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_4757_);
        v___x_4759_ = l_Lean_Syntax_isOfKind(v___x_4757_, v___x_4758_);
        if v___x_4759_ == 0 {
            let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4757_);
            lean_dec(v_x_4749_);
            v___x_4760_ = lean_box(0);
            v___x_4761_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_4761_, 0, v___x_4760_);
            lean_ctor_set(v___x_4761_, 1, v_a_4751_);
            return v___x_4761_;
        } else {
            let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4765_: u8 = 0;
            v___x_4762_ = lean_unsigned_to_nat(1);
            v___x_4763_ = l_Lean_Syntax_getArg(v_x_4749_, v___x_4762_);
            lean_dec(v_x_4749_);
            v___x_4764_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_4763_);
            v___x_4765_ = l_Lean_Syntax_matchesNull(v___x_4763_, v___x_4764_);
            if v___x_4765_ == 0 {
                let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4763_);
                lean_dec(v___x_4757_);
                v___x_4766_ = lean_box(0);
                v___x_4767_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4767_, 0, v___x_4766_);
                lean_ctor_set(v___x_4767_, 1, v_a_4751_);
                return v___x_4767_;
            } else {
                let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_4770_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4771_: u8 = 0;
                let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
                v___x_4768_ = l_Lean_Syntax_getArg(v___x_4763_, v___x_4756_);
                v___x_4769_ = l_Lean_Syntax_getArg(v___x_4763_, v___x_4762_);
                lean_dec(v___x_4763_);
                v_ref_4770_ = l_Lean_replaceRef(v___x_4757_, v_a_4750_);
                lean_dec(v___x_4757_);
                v___x_4771_ = 0;
                v___x_4772_ = l_Lean_SourceInfo_fromRef(v_ref_4770_, v___x_4771_);
                lean_dec(v_ref_4770_);
                v___x_4773_ = l_term___u2229___00__closed__1;
                v___x_4774_ = l_term___u2229___00__closed__2;
                lean_inc(v___x_4772_);
                v___x_4775_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4775_, 0, v___x_4772_);
                lean_ctor_set(v___x_4775_, 1, v___x_4774_);
                v___x_4776_ = l_Lean_Syntax_node3(
                    v___x_4772_,
                    v___x_4773_,
                    v___x_4768_,
                    v___x_4775_,
                    v___x_4769_,
                );
                v___x_4777_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4777_, 0, v___x_4776_);
                lean_ctor_set(v___x_4777_, 1, v_a_4751_);
                return v___x_4777_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__Inter__inter__1___boxed(
    mut v_x_4778_: *mut LeanObject,
    mut v_a_4779_: *mut LeanObject,
    mut v_a_4780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4781_: *mut LeanObject = core::ptr::null_mut();
    v_res_4781_ =
        l___aux__Init__Core______unexpand__Inter__inter__1(v_x_4778_, v_a_4779_, v_a_4780_);
    lean_dec(v_a_4779_);
    return v_res_4781_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1()
-> *mut LeanObject {
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    v___x_4799_ = l___aux__Init__Core______macroRules__term___x5c____1___closed__0;
    v___x_4800_ = l_String_toRawSubstring_x27(v___x_4799_);
    return v___x_4800_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___x5c____1(
    mut v_x_4812_: *mut LeanObject,
    mut v_a_4813_: *mut LeanObject,
    mut v_a_4814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: u8 = 0;
    v___x_4815_ = l_term___x5c___00__closed__1;
    lean_inc(v_x_4812_);
    v___x_4816_ = l_Lean_Syntax_isOfKind(v_x_4812_, v___x_4815_);
    if v___x_4816_ == 0 {
        let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4812_);
        v___x_4817_ = lean_box(1);
        v___x_4818_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4818_, 0, v___x_4817_);
        lean_ctor_set(v___x_4818_, 1, v_a_4814_);
        return v___x_4818_;
    } else {
        let mut v_quotContext_4819_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4820_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4826_: u8 = 0;
        let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4819_ = lean_ctor_get(v_a_4813_, 1);
        v_currMacroScope_4820_ = lean_ctor_get(v_a_4813_, 2);
        v_ref_4821_ = lean_ctor_get(v_a_4813_, 5);
        v___x_4822_ = lean_unsigned_to_nat(0);
        v___x_4823_ = l_Lean_Syntax_getArg(v_x_4812_, v___x_4822_);
        v___x_4824_ = lean_unsigned_to_nat(2);
        v___x_4825_ = l_Lean_Syntax_getArg(v_x_4812_, v___x_4824_);
        lean_dec(v_x_4812_);
        v___x_4826_ = 0;
        v___x_4827_ = l_Lean_SourceInfo_fromRef(v_ref_4821_, v___x_4826_);
        v___x_4828_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_4829_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x5c____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x5c____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1,
        );
        v___x_4830_ = l___aux__Init__Core______macroRules__term___x5c____1___closed__4;
        lean_inc(v_currMacroScope_4820_);
        lean_inc(v_quotContext_4819_);
        v___x_4831_ =
            l_Lean_addMacroScope(v_quotContext_4819_, v___x_4830_, v_currMacroScope_4820_);
        v___x_4832_ = l___aux__Init__Core______macroRules__term___x5c____1___closed__6;
        lean_inc_n(v___x_4827_, 2);
        v___x_4833_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4833_, 0, v___x_4827_);
        lean_ctor_set(v___x_4833_, 1, v___x_4829_);
        lean_ctor_set(v___x_4833_, 2, v___x_4831_);
        lean_ctor_set(v___x_4833_, 3, v___x_4832_);
        v___x_4834_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_4835_ = l_Lean_Syntax_node2(v___x_4827_, v___x_4834_, v___x_4823_, v___x_4825_);
        v___x_4836_ = l_Lean_Syntax_node2(v___x_4827_, v___x_4828_, v___x_4833_, v___x_4835_);
        v___x_4837_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4837_, 0, v___x_4836_);
        lean_ctor_set(v___x_4837_, 1, v_a_4814_);
        return v___x_4837_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___x5c____1___boxed(
    mut v_x_4838_: *mut LeanObject,
    mut v_a_4839_: *mut LeanObject,
    mut v_a_4840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4841_: *mut LeanObject = core::ptr::null_mut();
    v_res_4841_ =
        l___aux__Init__Core______macroRules__term___x5c____1(v_x_4838_, v_a_4839_, v_a_4840_);
    lean_dec_ref(v_a_4839_);
    return v_res_4841_;
}
pub unsafe fn l___aux__Init__Core______unexpand__SDiff__sdiff__1(
    mut v_x_4842_: *mut LeanObject,
    mut v_a_4843_: *mut LeanObject,
    mut v_a_4844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: u8 = 0;
    v___x_4845_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_4842_);
    v___x_4846_ = l_Lean_Syntax_isOfKind(v_x_4842_, v___x_4845_);
    if v___x_4846_ == 0 {
        let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4842_);
        v___x_4847_ = lean_box(0);
        v___x_4848_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4848_, 0, v___x_4847_);
        lean_ctor_set(v___x_4848_, 1, v_a_4844_);
        return v___x_4848_;
    } else {
        let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4852_: u8 = 0;
        v___x_4849_ = lean_unsigned_to_nat(0);
        v___x_4850_ = l_Lean_Syntax_getArg(v_x_4842_, v___x_4849_);
        v___x_4851_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_4850_);
        v___x_4852_ = l_Lean_Syntax_isOfKind(v___x_4850_, v___x_4851_);
        if v___x_4852_ == 0 {
            let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4850_);
            lean_dec(v_x_4842_);
            v___x_4853_ = lean_box(0);
            v___x_4854_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_4854_, 0, v___x_4853_);
            lean_ctor_set(v___x_4854_, 1, v_a_4844_);
            return v___x_4854_;
        } else {
            let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4858_: u8 = 0;
            v___x_4855_ = lean_unsigned_to_nat(1);
            v___x_4856_ = l_Lean_Syntax_getArg(v_x_4842_, v___x_4855_);
            lean_dec(v_x_4842_);
            v___x_4857_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_4856_);
            v___x_4858_ = l_Lean_Syntax_matchesNull(v___x_4856_, v___x_4857_);
            if v___x_4858_ == 0 {
                let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4856_);
                lean_dec(v___x_4850_);
                v___x_4859_ = lean_box(0);
                v___x_4860_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4860_, 0, v___x_4859_);
                lean_ctor_set(v___x_4860_, 1, v_a_4844_);
                return v___x_4860_;
            } else {
                let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_4863_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4864_: u8 = 0;
                let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
                v___x_4861_ = l_Lean_Syntax_getArg(v___x_4856_, v___x_4849_);
                v___x_4862_ = l_Lean_Syntax_getArg(v___x_4856_, v___x_4855_);
                lean_dec(v___x_4856_);
                v_ref_4863_ = l_Lean_replaceRef(v___x_4850_, v_a_4843_);
                lean_dec(v___x_4850_);
                v___x_4864_ = 0;
                v___x_4865_ = l_Lean_SourceInfo_fromRef(v_ref_4863_, v___x_4864_);
                lean_dec(v_ref_4863_);
                v___x_4866_ = l_term___x5c___00__closed__1;
                v___x_4867_ = l_term___x5c___00__closed__2;
                lean_inc(v___x_4865_);
                v___x_4868_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4868_, 0, v___x_4865_);
                lean_ctor_set(v___x_4868_, 1, v___x_4867_);
                v___x_4869_ = l_Lean_Syntax_node3(
                    v___x_4865_,
                    v___x_4866_,
                    v___x_4861_,
                    v___x_4868_,
                    v___x_4862_,
                );
                v___x_4870_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4870_, 0, v___x_4869_);
                lean_ctor_set(v___x_4870_, 1, v_a_4844_);
                return v___x_4870_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__SDiff__sdiff__1___boxed(
    mut v_x_4871_: *mut LeanObject,
    mut v_a_4872_: *mut LeanObject,
    mut v_a_4873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4874_: *mut LeanObject = core::ptr::null_mut();
    v_res_4874_ =
        l___aux__Init__Core______unexpand__SDiff__sdiff__1(v_x_4871_, v_a_4872_, v_a_4873_);
    lean_dec(v_a_4872_);
    return v_res_4874_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    v___x_4894_ = l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0;
    v___x_4895_ = l_String_toRawSubstring_x27(v___x_4894_);
    return v___x_4895_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term_x7b_x7d__1(
    mut v_x_4907_: *mut LeanObject,
    mut v_a_4908_: *mut LeanObject,
    mut v_a_4909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: u8 = 0;
    v___x_4910_ = l_term_x7b_x7d___closed__1;
    v___x_4911_ = l_Lean_Syntax_isOfKind(v_x_4907_, v___x_4910_);
    if v___x_4911_ == 0 {
        let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
        v___x_4912_ = lean_box(1);
        v___x_4913_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4913_, 0, v___x_4912_);
        lean_ctor_set(v___x_4913_, 1, v_a_4909_);
        return v___x_4913_;
    } else {
        let mut v_quotContext_4914_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4915_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4917_: u8 = 0;
        let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4914_ = lean_ctor_get(v_a_4908_, 1);
        v_currMacroScope_4915_ = lean_ctor_get(v_a_4908_, 2);
        v_ref_4916_ = lean_ctor_get(v_a_4908_, 5);
        v___x_4917_ = 0;
        v___x_4918_ = l_Lean_SourceInfo_fromRef(v_ref_4916_, v___x_4917_);
        v___x_4919_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1,
        );
        v___x_4920_ = l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4;
        lean_inc(v_currMacroScope_4915_);
        lean_inc(v_quotContext_4914_);
        v___x_4921_ =
            l_Lean_addMacroScope(v_quotContext_4914_, v___x_4920_, v_currMacroScope_4915_);
        v___x_4922_ = l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6;
        v___x_4923_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4923_, 0, v___x_4918_);
        lean_ctor_set(v___x_4923_, 1, v___x_4919_);
        lean_ctor_set(v___x_4923_, 2, v___x_4921_);
        lean_ctor_set(v___x_4923_, 3, v___x_4922_);
        v___x_4924_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4924_, 0, v___x_4923_);
        lean_ctor_set(v___x_4924_, 1, v_a_4909_);
        return v___x_4924_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term_x7b_x7d__1___boxed(
    mut v_x_4925_: *mut LeanObject,
    mut v_a_4926_: *mut LeanObject,
    mut v_a_4927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4928_: *mut LeanObject = core::ptr::null_mut();
    v_res_4928_ =
        l___aux__Init__Core______macroRules__term_x7b_x7d__1(v_x_4925_, v_a_4926_, v_a_4927_);
    lean_dec_ref(v_a_4926_);
    return v_res_4928_;
}
pub unsafe fn l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(
    mut v_x_4929_: *mut LeanObject,
    mut v_a_4930_: *mut LeanObject,
    mut v_a_4931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: u8 = 0;
    v___x_4932_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
    lean_inc(v_x_4929_);
    v___x_4933_ = l_Lean_Syntax_isOfKind(v_x_4929_, v___x_4932_);
    if v___x_4933_ == 0 {
        let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4929_);
        v___x_4934_ = lean_box(0);
        v___x_4935_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4935_, 0, v___x_4934_);
        lean_ctor_set(v___x_4935_, 1, v_a_4931_);
        return v___x_4935_;
    } else {
        let mut v_ref_4936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4937_: u8 = 0;
        let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4936_ = l_Lean_replaceRef(v_x_4929_, v_a_4930_);
        lean_dec(v_x_4929_);
        v___x_4937_ = 0;
        v___x_4938_ = l_Lean_SourceInfo_fromRef(v_ref_4936_, v___x_4937_);
        lean_dec(v_ref_4936_);
        v___x_4939_ = l_term_x7b_x7d___closed__1;
        v___x_4940_ = l_term_x7b_x7d___closed__2;
        lean_inc_n(v___x_4938_, 2);
        v___x_4941_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4941_, 0, v___x_4938_);
        lean_ctor_set(v___x_4941_, 1, v___x_4940_);
        v___x_4942_ = l_term_x7b_x7d___closed__4;
        v___x_4943_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4943_, 0, v___x_4938_);
        lean_ctor_set(v___x_4943_, 1, v___x_4942_);
        v___x_4944_ = l_Lean_Syntax_node2(v___x_4938_, v___x_4939_, v___x_4941_, v___x_4943_);
        v___x_4945_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4945_, 0, v___x_4944_);
        lean_ctor_set(v___x_4945_, 1, v_a_4931_);
        return v___x_4945_;
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1___boxed(
    mut v_x_4946_: *mut LeanObject,
    mut v_a_4947_: *mut LeanObject,
    mut v_a_4948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4949_: *mut LeanObject = core::ptr::null_mut();
    v_res_4949_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(
        v_x_4946_, v_a_4947_, v_a_4948_,
    );
    lean_dec(v_a_4947_);
    return v_res_4949_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term_u2205__1(
    mut v_x_4961_: *mut LeanObject,
    mut v_a_4962_: *mut LeanObject,
    mut v_a_4963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: u8 = 0;
    v___x_4964_ = l_term_u2205___closed__1;
    v___x_4965_ = l_Lean_Syntax_isOfKind(v_x_4961_, v___x_4964_);
    if v___x_4965_ == 0 {
        let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
        v___x_4966_ = lean_box(1);
        v___x_4967_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4967_, 0, v___x_4966_);
        lean_ctor_set(v___x_4967_, 1, v_a_4963_);
        return v___x_4967_;
    } else {
        let mut v_quotContext_4968_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4969_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4971_: u8 = 0;
        let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4968_ = lean_ctor_get(v_a_4962_, 1);
        v_currMacroScope_4969_ = lean_ctor_get(v_a_4962_, 2);
        v_ref_4970_ = lean_ctor_get(v_a_4962_, 5);
        v___x_4971_ = 0;
        v___x_4972_ = l_Lean_SourceInfo_fromRef(v_ref_4970_, v___x_4971_);
        v___x_4973_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1,
        );
        v___x_4974_ = l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4;
        lean_inc(v_currMacroScope_4969_);
        lean_inc(v_quotContext_4968_);
        v___x_4975_ =
            l_Lean_addMacroScope(v_quotContext_4968_, v___x_4974_, v_currMacroScope_4969_);
        v___x_4976_ = l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6;
        v___x_4977_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4977_, 0, v___x_4972_);
        lean_ctor_set(v___x_4977_, 1, v___x_4973_);
        lean_ctor_set(v___x_4977_, 2, v___x_4975_);
        lean_ctor_set(v___x_4977_, 3, v___x_4976_);
        v___x_4978_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4978_, 0, v___x_4977_);
        lean_ctor_set(v___x_4978_, 1, v_a_4963_);
        return v___x_4978_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term_u2205__1___boxed(
    mut v_x_4979_: *mut LeanObject,
    mut v_a_4980_: *mut LeanObject,
    mut v_a_4981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4982_: *mut LeanObject = core::ptr::null_mut();
    v_res_4982_ =
        l___aux__Init__Core______macroRules__term_u2205__1(v_x_4979_, v_a_4980_, v_a_4981_);
    lean_dec_ref(v_a_4980_);
    return v_res_4982_;
}
pub unsafe fn l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(
    mut v_x_4983_: *mut LeanObject,
    mut v_a_4984_: *mut LeanObject,
    mut v_a_4985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: u8 = 0;
    v___x_4986_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
    lean_inc(v_x_4983_);
    v___x_4987_ = l_Lean_Syntax_isOfKind(v_x_4983_, v___x_4986_);
    if v___x_4987_ == 0 {
        let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4983_);
        v___x_4988_ = lean_box(0);
        v___x_4989_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4989_, 0, v___x_4988_);
        lean_ctor_set(v___x_4989_, 1, v_a_4985_);
        return v___x_4989_;
    } else {
        let mut v_ref_4990_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4991_: u8 = 0;
        let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4990_ = l_Lean_replaceRef(v_x_4983_, v_a_4984_);
        lean_dec(v_x_4983_);
        v___x_4991_ = 0;
        v___x_4992_ = l_Lean_SourceInfo_fromRef(v_ref_4990_, v___x_4991_);
        lean_dec(v_ref_4990_);
        v___x_4993_ = l_term_u2205___closed__1;
        v___x_4994_ = l_term_u2205___closed__2;
        lean_inc(v___x_4992_);
        v___x_4995_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4995_, 0, v___x_4992_);
        lean_ctor_set(v___x_4995_, 1, v___x_4994_);
        v___x_4996_ = l_Lean_Syntax_node1(v___x_4992_, v___x_4993_, v___x_4995_);
        v___x_4997_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4997_, 0, v___x_4996_);
        lean_ctor_set(v___x_4997_, 1, v_a_4985_);
        return v___x_4997_;
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2___boxed(
    mut v_x_4998_: *mut LeanObject,
    mut v_a_4999_: *mut LeanObject,
    mut v_a_5000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5001_: *mut LeanObject = core::ptr::null_mut();
    v_res_5001_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(
        v_x_4998_, v_a_4999_, v_a_5000_,
    );
    lean_dec(v_a_4999_);
    return v_res_5001_;
}
pub unsafe fn l_instInhabitedTask_default___redArg(
    mut v_inst_5002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    v___x_5003_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5003_, 0, v_inst_5002_);
    return v___x_5003_;
}
pub unsafe fn l_instInhabitedTask_default(
    mut v_00_u03b1_5004_: *mut LeanObject,
    mut v_inst_5005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    v___x_5006_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5006_, 0, v_inst_5005_);
    return v___x_5006_;
}
pub unsafe fn l_instInhabitedTask___redArg(mut v_inst_5007_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    v___x_5008_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5008_, 0, v_inst_5007_);
    return v___x_5008_;
}
pub unsafe fn l_instInhabitedTask(
    mut v_a_5009_: *mut LeanObject,
    mut v_inst_5010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    v___x_5011_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5011_, 0, v_inst_5010_);
    return v___x_5011_;
}
pub unsafe fn l_Task_pure___boxed(
    mut v_00_u03b1_5014_: *mut LeanObject,
    mut v_get_5015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5016_: *mut LeanObject = core::ptr::null_mut();
    v_res_5016_ = lean_task_pure(v_get_5015_);
    return v_res_5016_;
}
pub unsafe fn l_Task_get___boxed(
    mut v_00_u03b1_5019_: *mut LeanObject,
    mut v_self_5020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5021_: *mut LeanObject = core::ptr::null_mut();
    v_res_5021_ = lean_task_get_own(v_self_5020_);
    return v_res_5021_;
}
pub unsafe fn _init_l_Task_Priority_default() -> *mut LeanObject {
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    v___x_5022_ = lean_unsigned_to_nat(0);
    return v___x_5022_;
}
pub unsafe fn _init_l_Task_Priority_max() -> *mut LeanObject {
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    v___x_5023_ = lean_unsigned_to_nat(8);
    return v___x_5023_;
}
pub unsafe fn _init_l_Task_Priority_dedicated() -> *mut LeanObject {
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    v___x_5024_ = lean_unsigned_to_nat(9);
    return v___x_5024_;
}
pub unsafe fn l_Task_spawn___boxed(
    mut v_00_u03b1_5028_: *mut LeanObject,
    mut v_fn_5029_: *mut LeanObject,
    mut v_prio_5030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5031_: *mut LeanObject = core::ptr::null_mut();
    v_res_5031_ = lean_task_spawn(v_fn_5029_, v_prio_5030_);
    return v_res_5031_;
}
pub unsafe fn l_Task_map___boxed(
    mut v_00_u03b1_5038_: *mut LeanObject,
    mut v_00_u03b2_5039_: *mut LeanObject,
    mut v_f_5040_: *mut LeanObject,
    mut v_x_5041_: *mut LeanObject,
    mut v_prio_5042_: *mut LeanObject,
    mut v_sync_5043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5044_: u8 = 0;
    let mut v_res_5045_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5044_ = (lean_unbox(v_sync_5043_) as u8);
    v_res_5045_ = lean_task_map(v_f_5040_, v_x_5041_, v_prio_5042_, v_sync_boxed_5044_);
    return v_res_5045_;
}
pub unsafe fn l_Task_bind___boxed(
    mut v_00_u03b1_5052_: *mut LeanObject,
    mut v_00_u03b2_5053_: *mut LeanObject,
    mut v_x_5054_: *mut LeanObject,
    mut v_f_5055_: *mut LeanObject,
    mut v_prio_5056_: *mut LeanObject,
    mut v_sync_5057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5058_: u8 = 0;
    let mut v_res_5059_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5058_ = (lean_unbox(v_sync_5057_) as u8);
    v_res_5059_ = lean_task_bind(v_x_5054_, v_f_5055_, v_prio_5056_, v_sync_boxed_5058_);
    return v_res_5059_;
}
pub unsafe fn l_strictOr___boxed(
    mut v_b_u2081_5062_: *mut LeanObject,
    mut v_b_u2082_5063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_u2081_boxed_5064_: u8 = 0;
    let mut v_b_u2082_boxed_5065_: u8 = 0;
    let mut v_res_5066_: u8 = 0;
    let mut v_r_5067_: *mut LeanObject = core::ptr::null_mut();
    v_b_u2081_boxed_5064_ = (lean_unbox(v_b_u2081_5062_) as u8);
    v_b_u2082_boxed_5065_ = (lean_unbox(v_b_u2082_5063_) as u8);
    v_res_5066_ = lean_strict_or(v_b_u2081_boxed_5064_, v_b_u2082_boxed_5065_);
    v_r_5067_ = lean_box((v_res_5066_) as usize);
    return v_r_5067_;
}
pub unsafe fn l_strictAnd___boxed(
    mut v_b_u2081_5070_: *mut LeanObject,
    mut v_b_u2082_5071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_u2081_boxed_5072_: u8 = 0;
    let mut v_b_u2082_boxed_5073_: u8 = 0;
    let mut v_res_5074_: u8 = 0;
    let mut v_r_5075_: *mut LeanObject = core::ptr::null_mut();
    v_b_u2081_boxed_5072_ = (lean_unbox(v_b_u2081_5070_) as u8);
    v_b_u2082_boxed_5073_ = (lean_unbox(v_b_u2082_5071_) as u8);
    v_res_5074_ = lean_strict_and(v_b_u2081_boxed_5072_, v_b_u2082_boxed_5073_);
    v_r_5075_ = lean_box((v_res_5074_) as usize);
    return v_r_5075_;
}
pub unsafe fn l_bne___redArg(
    mut v_inst_5076_: *mut LeanObject,
    mut v_a_5077_: *mut LeanObject,
    mut v_b_5078_: *mut LeanObject,
) -> u8 {
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: u8 = 0;
    v___x_5079_ = lean_apply_2(v_inst_5076_, v_a_5077_, v_b_5078_);
    v___x_5080_ = (lean_unbox(v___x_5079_) as u8);
    if v___x_5080_ == 0 {
        let mut v___x_5081_: u8 = 0;
        v___x_5081_ = 1;
        return v___x_5081_;
    } else {
        let mut v___x_5082_: u8 = 0;
        v___x_5082_ = 0;
        return v___x_5082_;
    }
}
pub unsafe fn l_bne___redArg___boxed(
    mut v_inst_5083_: *mut LeanObject,
    mut v_a_5084_: *mut LeanObject,
    mut v_b_5085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5086_: u8 = 0;
    let mut v_r_5087_: *mut LeanObject = core::ptr::null_mut();
    v_res_5086_ = l_bne___redArg(v_inst_5083_, v_a_5084_, v_b_5085_);
    v_r_5087_ = lean_box((v_res_5086_) as usize);
    return v_r_5087_;
}
pub unsafe fn l_bne(
    mut v_00_u03b1_5088_: *mut LeanObject,
    mut v_inst_5089_: *mut LeanObject,
    mut v_a_5090_: *mut LeanObject,
    mut v_b_5091_: *mut LeanObject,
) -> u8 {
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: u8 = 0;
    v___x_5092_ = lean_apply_2(v_inst_5089_, v_a_5090_, v_b_5091_);
    v___x_5093_ = (lean_unbox(v___x_5092_) as u8);
    if v___x_5093_ == 0 {
        let mut v___x_5094_: u8 = 0;
        v___x_5094_ = 1;
        return v___x_5094_;
    } else {
        let mut v___x_5095_: u8 = 0;
        v___x_5095_ = 0;
        return v___x_5095_;
    }
}
pub unsafe fn l_bne___boxed(
    mut v_00_u03b1_5096_: *mut LeanObject,
    mut v_inst_5097_: *mut LeanObject,
    mut v_a_5098_: *mut LeanObject,
    mut v_b_5099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5100_: u8 = 0;
    let mut v_r_5101_: *mut LeanObject = core::ptr::null_mut();
    v_res_5100_ = l_bne(v_00_u03b1_5096_, v_inst_5097_, v_a_5098_, v_b_5099_);
    v_r_5101_ = lean_box((v_res_5100_) as usize);
    return v_r_5101_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1()
-> *mut LeanObject {
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    v___x_5119_ = l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0;
    v___x_5120_ = l_String_toRawSubstring_x27(v___x_5119_);
    return v___x_5120_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___x21_x3d____1(
    mut v_x_5129_: *mut LeanObject,
    mut v_a_5130_: *mut LeanObject,
    mut v_a_5131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: u8 = 0;
    v___x_5132_ = l_term___x21_x3d___00__closed__1;
    lean_inc(v_x_5129_);
    v___x_5133_ = l_Lean_Syntax_isOfKind(v_x_5129_, v___x_5132_);
    if v___x_5133_ == 0 {
        let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5129_);
        v___x_5134_ = lean_box(1);
        v___x_5135_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5135_, 0, v___x_5134_);
        lean_ctor_set(v___x_5135_, 1, v_a_5131_);
        return v___x_5135_;
    } else {
        let mut v_quotContext_5136_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5137_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_5138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5143_: u8 = 0;
        let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_5136_ = lean_ctor_get(v_a_5130_, 1);
        v_currMacroScope_5137_ = lean_ctor_get(v_a_5130_, 2);
        v_ref_5138_ = lean_ctor_get(v_a_5130_, 5);
        v___x_5139_ = lean_unsigned_to_nat(0);
        v___x_5140_ = l_Lean_Syntax_getArg(v_x_5129_, v___x_5139_);
        v___x_5141_ = lean_unsigned_to_nat(2);
        v___x_5142_ = l_Lean_Syntax_getArg(v_x_5129_, v___x_5141_);
        lean_dec(v_x_5129_);
        v___x_5143_ = 0;
        v___x_5144_ = l_Lean_SourceInfo_fromRef(v_ref_5138_, v___x_5143_);
        v___x_5145_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_5146_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1,
        );
        v___x_5147_ = l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2;
        lean_inc(v_currMacroScope_5137_);
        lean_inc(v_quotContext_5136_);
        v___x_5148_ =
            l_Lean_addMacroScope(v_quotContext_5136_, v___x_5147_, v_currMacroScope_5137_);
        v___x_5149_ = l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4;
        lean_inc_n(v___x_5144_, 2);
        v___x_5150_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_5150_, 0, v___x_5144_);
        lean_ctor_set(v___x_5150_, 1, v___x_5146_);
        lean_ctor_set(v___x_5150_, 2, v___x_5148_);
        lean_ctor_set(v___x_5150_, 3, v___x_5149_);
        v___x_5151_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_5152_ = l_Lean_Syntax_node2(v___x_5144_, v___x_5151_, v___x_5140_, v___x_5142_);
        v___x_5153_ = l_Lean_Syntax_node2(v___x_5144_, v___x_5145_, v___x_5150_, v___x_5152_);
        v___x_5154_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5154_, 0, v___x_5153_);
        lean_ctor_set(v___x_5154_, 1, v_a_5131_);
        return v___x_5154_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___x21_x3d____1___boxed(
    mut v_x_5155_: *mut LeanObject,
    mut v_a_5156_: *mut LeanObject,
    mut v_a_5157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5158_: *mut LeanObject = core::ptr::null_mut();
    v_res_5158_ =
        l___aux__Init__Core______macroRules__term___x21_x3d____1(v_x_5155_, v_a_5156_, v_a_5157_);
    lean_dec_ref(v_a_5156_);
    return v_res_5158_;
}
pub unsafe fn l___aux__Init__Core______unexpand__bne__1(
    mut v_x_5159_: *mut LeanObject,
    mut v_a_5160_: *mut LeanObject,
    mut v_a_5161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: u8 = 0;
    v___x_5162_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_5159_);
    v___x_5163_ = l_Lean_Syntax_isOfKind(v_x_5159_, v___x_5162_);
    if v___x_5163_ == 0 {
        let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5159_);
        v___x_5164_ = lean_box(0);
        v___x_5165_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5165_, 0, v___x_5164_);
        lean_ctor_set(v___x_5165_, 1, v_a_5161_);
        return v___x_5165_;
    } else {
        let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5169_: u8 = 0;
        v___x_5166_ = lean_unsigned_to_nat(0);
        v___x_5167_ = l_Lean_Syntax_getArg(v_x_5159_, v___x_5166_);
        v___x_5168_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_5167_);
        v___x_5169_ = l_Lean_Syntax_isOfKind(v___x_5167_, v___x_5168_);
        if v___x_5169_ == 0 {
            let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_5167_);
            lean_dec(v_x_5159_);
            v___x_5170_ = lean_box(0);
            v___x_5171_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_5171_, 0, v___x_5170_);
            lean_ctor_set(v___x_5171_, 1, v_a_5161_);
            return v___x_5171_;
        } else {
            let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5175_: u8 = 0;
            v___x_5172_ = lean_unsigned_to_nat(1);
            v___x_5173_ = l_Lean_Syntax_getArg(v_x_5159_, v___x_5172_);
            lean_dec(v_x_5159_);
            v___x_5174_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_5173_);
            v___x_5175_ = l_Lean_Syntax_matchesNull(v___x_5173_, v___x_5174_);
            if v___x_5175_ == 0 {
                let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_5173_);
                lean_dec(v___x_5167_);
                v___x_5176_ = lean_box(0);
                v___x_5177_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5177_, 0, v___x_5176_);
                lean_ctor_set(v___x_5177_, 1, v_a_5161_);
                return v___x_5177_;
            } else {
                let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_5180_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5181_: u8 = 0;
                let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
                v___x_5178_ = l_Lean_Syntax_getArg(v___x_5173_, v___x_5166_);
                v___x_5179_ = l_Lean_Syntax_getArg(v___x_5173_, v___x_5172_);
                lean_dec(v___x_5173_);
                v_ref_5180_ = l_Lean_replaceRef(v___x_5167_, v_a_5160_);
                lean_dec(v___x_5167_);
                v___x_5181_ = 0;
                v___x_5182_ = l_Lean_SourceInfo_fromRef(v_ref_5180_, v___x_5181_);
                lean_dec(v_ref_5180_);
                v___x_5183_ = l_term___x21_x3d___00__closed__1;
                v___x_5184_ = l_term___x21_x3d___00__closed__2;
                lean_inc(v___x_5182_);
                v___x_5185_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5185_, 0, v___x_5182_);
                lean_ctor_set(v___x_5185_, 1, v___x_5184_);
                v___x_5186_ = l_Lean_Syntax_node3(
                    v___x_5182_,
                    v___x_5183_,
                    v___x_5178_,
                    v___x_5185_,
                    v___x_5179_,
                );
                v___x_5187_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5187_, 0, v___x_5186_);
                lean_ctor_set(v___x_5187_, 1, v_a_5161_);
                return v___x_5187_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__bne__1___boxed(
    mut v_x_5188_: *mut LeanObject,
    mut v_a_5189_: *mut LeanObject,
    mut v_a_5190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5191_: *mut LeanObject = core::ptr::null_mut();
    v_res_5191_ = l___aux__Init__Core______unexpand__bne__1(v_x_5188_, v_a_5189_, v_a_5190_);
    lean_dec(v_a_5189_);
    return v_res_5191_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___x21_x3d____2(
    mut v_x_5199_: *mut LeanObject,
    mut v_a_5200_: *mut LeanObject,
    mut v_a_5201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: u8 = 0;
    v___x_5202_ = l_term___x21_x3d___00__closed__1;
    lean_inc(v_x_5199_);
    v___x_5203_ = l_Lean_Syntax_isOfKind(v_x_5199_, v___x_5202_);
    if v___x_5203_ == 0 {
        let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5199_);
        v___x_5204_ = lean_box(1);
        v___x_5205_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5205_, 0, v___x_5204_);
        lean_ctor_set(v___x_5205_, 1, v_a_5201_);
        return v___x_5205_;
    } else {
        let mut v_quotContext_5206_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5207_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_5208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5213_: u8 = 0;
        let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_5206_ = lean_ctor_get(v_a_5200_, 1);
        v_currMacroScope_5207_ = lean_ctor_get(v_a_5200_, 2);
        v_ref_5208_ = lean_ctor_get(v_a_5200_, 5);
        v___x_5209_ = lean_unsigned_to_nat(0);
        v___x_5210_ = l_Lean_Syntax_getArg(v_x_5199_, v___x_5209_);
        v___x_5211_ = lean_unsigned_to_nat(2);
        v___x_5212_ = l_Lean_Syntax_getArg(v_x_5199_, v___x_5211_);
        lean_dec(v_x_5199_);
        v___x_5213_ = 0;
        v___x_5214_ = l_Lean_SourceInfo_fromRef(v_ref_5208_, v___x_5213_);
        v___x_5215_ = l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1;
        v___x_5216_ = l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2;
        lean_inc_n(v___x_5214_, 2);
        v___x_5217_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5217_, 0, v___x_5214_);
        lean_ctor_set(v___x_5217_, 1, v___x_5216_);
        v___x_5218_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1,
        );
        v___x_5219_ = l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2;
        lean_inc(v_currMacroScope_5207_);
        lean_inc(v_quotContext_5206_);
        v___x_5220_ =
            l_Lean_addMacroScope(v_quotContext_5206_, v___x_5219_, v_currMacroScope_5207_);
        v___x_5221_ = l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4;
        v___x_5222_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_5222_, 0, v___x_5214_);
        lean_ctor_set(v___x_5222_, 1, v___x_5218_);
        lean_ctor_set(v___x_5222_, 2, v___x_5220_);
        lean_ctor_set(v___x_5222_, 3, v___x_5221_);
        v___x_5223_ = l_Lean_Syntax_node4(
            v___x_5214_,
            v___x_5215_,
            v___x_5217_,
            v___x_5222_,
            v___x_5210_,
            v___x_5212_,
        );
        v___x_5224_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5224_, 0, v___x_5223_);
        lean_ctor_set(v___x_5224_, 1, v_a_5201_);
        return v___x_5224_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___x21_x3d____2___boxed(
    mut v_x_5225_: *mut LeanObject,
    mut v_a_5226_: *mut LeanObject,
    mut v_a_5227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5228_: *mut LeanObject = core::ptr::null_mut();
    v_res_5228_ =
        l___aux__Init__Core______macroRules__term___x21_x3d____2(v_x_5225_, v_a_5226_, v_a_5227_);
    lean_dec_ref(v_a_5226_);
    return v_res_5228_;
}
pub unsafe fn l_instDecidableEqOfLawfulBEq___redArg(
    mut v_inst_5229_: *mut LeanObject,
    mut v_x_5230_: *mut LeanObject,
    mut v_y_5231_: *mut LeanObject,
) -> u8 {
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: u8 = 0;
    v___x_5232_ = lean_apply_2(v_inst_5229_, v_x_5230_, v_y_5231_);
    v___x_5233_ = (lean_unbox(v___x_5232_) as u8);
    return v___x_5233_;
}
pub unsafe fn l_instDecidableEqOfLawfulBEq___redArg___boxed(
    mut v_inst_5234_: *mut LeanObject,
    mut v_x_5235_: *mut LeanObject,
    mut v_y_5236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5237_: u8 = 0;
    let mut v_r_5238_: *mut LeanObject = core::ptr::null_mut();
    v_res_5237_ = l_instDecidableEqOfLawfulBEq___redArg(v_inst_5234_, v_x_5235_, v_y_5236_);
    v_r_5238_ = lean_box((v_res_5237_) as usize);
    return v_r_5238_;
}
pub unsafe fn l_instDecidableEqOfLawfulBEq(
    mut v_00_u03b1_5239_: *mut LeanObject,
    mut v_inst_5240_: *mut LeanObject,
    mut v_inst_5241_: *mut LeanObject,
    mut v_x_5242_: *mut LeanObject,
    mut v_y_5243_: *mut LeanObject,
) -> u8 {
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    v___x_5244_ = lean_apply_2(v_inst_5240_, v_x_5242_, v_y_5243_);
    v___x_5245_ = (lean_unbox(v___x_5244_) as u8);
    return v___x_5245_;
}
pub unsafe fn l_instDecidableEqOfLawfulBEq___boxed(
    mut v_00_u03b1_5246_: *mut LeanObject,
    mut v_inst_5247_: *mut LeanObject,
    mut v_inst_5248_: *mut LeanObject,
    mut v_x_5249_: *mut LeanObject,
    mut v_y_5250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5251_: u8 = 0;
    let mut v_r_5252_: *mut LeanObject = core::ptr::null_mut();
    v_res_5251_ = l_instDecidableEqOfLawfulBEq(
        v_00_u03b1_5246_,
        v_inst_5247_,
        v_inst_5248_,
        v_x_5249_,
        v_y_5250_,
    );
    v_r_5252_ = lean_box((v_res_5251_) as usize);
    return v_r_5252_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1()
-> *mut LeanObject {
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    v___x_5270_ = l___aux__Init__Core______macroRules__term___u2260____1___closed__0;
    v___x_5271_ = l_String_toRawSubstring_x27(v___x_5270_);
    return v___x_5271_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2260____1(
    mut v_x_5280_: *mut LeanObject,
    mut v_a_5281_: *mut LeanObject,
    mut v_a_5282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: u8 = 0;
    v___x_5283_ = l_term___u2260___00__closed__1;
    lean_inc(v_x_5280_);
    v___x_5284_ = l_Lean_Syntax_isOfKind(v_x_5280_, v___x_5283_);
    if v___x_5284_ == 0 {
        let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5280_);
        v___x_5285_ = lean_box(1);
        v___x_5286_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5286_, 0, v___x_5285_);
        lean_ctor_set(v___x_5286_, 1, v_a_5282_);
        return v___x_5286_;
    } else {
        let mut v_quotContext_5287_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5288_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_5289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5294_: u8 = 0;
        let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_5287_ = lean_ctor_get(v_a_5281_, 1);
        v_currMacroScope_5288_ = lean_ctor_get(v_a_5281_, 2);
        v_ref_5289_ = lean_ctor_get(v_a_5281_, 5);
        v___x_5290_ = lean_unsigned_to_nat(0);
        v___x_5291_ = l_Lean_Syntax_getArg(v_x_5280_, v___x_5290_);
        v___x_5292_ = lean_unsigned_to_nat(2);
        v___x_5293_ = l_Lean_Syntax_getArg(v_x_5280_, v___x_5292_);
        lean_dec(v_x_5280_);
        v___x_5294_ = 0;
        v___x_5295_ = l_Lean_SourceInfo_fromRef(v_ref_5289_, v___x_5294_);
        v___x_5296_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
        v___x_5297_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2260____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1,
        );
        v___x_5298_ = l___aux__Init__Core______macroRules__term___u2260____1___closed__2;
        lean_inc(v_currMacroScope_5288_);
        lean_inc(v_quotContext_5287_);
        v___x_5299_ =
            l_Lean_addMacroScope(v_quotContext_5287_, v___x_5298_, v_currMacroScope_5288_);
        v___x_5300_ = l___aux__Init__Core______macroRules__term___u2260____1___closed__4;
        lean_inc_n(v___x_5295_, 2);
        v___x_5301_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_5301_, 0, v___x_5295_);
        lean_ctor_set(v___x_5301_, 1, v___x_5297_);
        lean_ctor_set(v___x_5301_, 2, v___x_5299_);
        lean_ctor_set(v___x_5301_, 3, v___x_5300_);
        v___x_5302_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13;
        v___x_5303_ = l_Lean_Syntax_node2(v___x_5295_, v___x_5302_, v___x_5291_, v___x_5293_);
        v___x_5304_ = l_Lean_Syntax_node2(v___x_5295_, v___x_5296_, v___x_5301_, v___x_5303_);
        v___x_5305_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5305_, 0, v___x_5304_);
        lean_ctor_set(v___x_5305_, 1, v_a_5282_);
        return v___x_5305_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2260____1___boxed(
    mut v_x_5306_: *mut LeanObject,
    mut v_a_5307_: *mut LeanObject,
    mut v_a_5308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5309_: *mut LeanObject = core::ptr::null_mut();
    v_res_5309_ =
        l___aux__Init__Core______macroRules__term___u2260____1(v_x_5306_, v_a_5307_, v_a_5308_);
    lean_dec_ref(v_a_5307_);
    return v_res_5309_;
}
pub unsafe fn l___aux__Init__Core______unexpand__Ne__1(
    mut v_x_5310_: *mut LeanObject,
    mut v_a_5311_: *mut LeanObject,
    mut v_a_5312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: u8 = 0;
    v___x_5313_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4;
    lean_inc(v_x_5310_);
    v___x_5314_ = l_Lean_Syntax_isOfKind(v_x_5310_, v___x_5313_);
    if v___x_5314_ == 0 {
        let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5310_);
        v___x_5315_ = lean_box(0);
        v___x_5316_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5316_, 0, v___x_5315_);
        lean_ctor_set(v___x_5316_, 1, v_a_5312_);
        return v___x_5316_;
    } else {
        let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5320_: u8 = 0;
        v___x_5317_ = lean_unsigned_to_nat(0);
        v___x_5318_ = l_Lean_Syntax_getArg(v_x_5310_, v___x_5317_);
        v___x_5319_ = l___aux__Init__Core______unexpand__Iff__1___closed__1;
        lean_inc(v___x_5318_);
        v___x_5320_ = l_Lean_Syntax_isOfKind(v___x_5318_, v___x_5319_);
        if v___x_5320_ == 0 {
            let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_5318_);
            lean_dec(v_x_5310_);
            v___x_5321_ = lean_box(0);
            v___x_5322_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_5322_, 0, v___x_5321_);
            lean_ctor_set(v___x_5322_, 1, v_a_5312_);
            return v___x_5322_;
        } else {
            let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5326_: u8 = 0;
            v___x_5323_ = lean_unsigned_to_nat(1);
            v___x_5324_ = l_Lean_Syntax_getArg(v_x_5310_, v___x_5323_);
            lean_dec(v_x_5310_);
            v___x_5325_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_5324_);
            v___x_5326_ = l_Lean_Syntax_matchesNull(v___x_5324_, v___x_5325_);
            if v___x_5326_ == 0 {
                let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_5324_);
                lean_dec(v___x_5318_);
                v___x_5327_ = lean_box(0);
                v___x_5328_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5328_, 0, v___x_5327_);
                lean_ctor_set(v___x_5328_, 1, v_a_5312_);
                return v___x_5328_;
            } else {
                let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_5331_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5332_: u8 = 0;
                let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
                v___x_5329_ = l_Lean_Syntax_getArg(v___x_5324_, v___x_5317_);
                v___x_5330_ = l_Lean_Syntax_getArg(v___x_5324_, v___x_5323_);
                lean_dec(v___x_5324_);
                v_ref_5331_ = l_Lean_replaceRef(v___x_5318_, v_a_5311_);
                lean_dec(v___x_5318_);
                v___x_5332_ = 0;
                v___x_5333_ = l_Lean_SourceInfo_fromRef(v_ref_5331_, v___x_5332_);
                lean_dec(v_ref_5331_);
                v___x_5334_ = l_term___u2260___00__closed__1;
                v___x_5335_ = l_term___u2260___00__closed__2;
                lean_inc(v___x_5333_);
                v___x_5336_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5336_, 0, v___x_5333_);
                lean_ctor_set(v___x_5336_, 1, v___x_5335_);
                v___x_5337_ = l_Lean_Syntax_node3(
                    v___x_5333_,
                    v___x_5334_,
                    v___x_5329_,
                    v___x_5336_,
                    v___x_5330_,
                );
                v___x_5338_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5338_, 0, v___x_5337_);
                lean_ctor_set(v___x_5338_, 1, v_a_5312_);
                return v___x_5338_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Core______unexpand__Ne__1___boxed(
    mut v_x_5339_: *mut LeanObject,
    mut v_a_5340_: *mut LeanObject,
    mut v_a_5341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5342_: *mut LeanObject = core::ptr::null_mut();
    v_res_5342_ = l___aux__Init__Core______unexpand__Ne__1(v_x_5339_, v_a_5340_, v_a_5341_);
    lean_dec(v_a_5340_);
    return v_res_5342_;
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2260____2(
    mut v_x_5350_: *mut LeanObject,
    mut v_a_5351_: *mut LeanObject,
    mut v_a_5352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: u8 = 0;
    v___x_5353_ = l_term___u2260___00__closed__1;
    lean_inc(v_x_5350_);
    v___x_5354_ = l_Lean_Syntax_isOfKind(v_x_5350_, v___x_5353_);
    if v___x_5354_ == 0 {
        let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5356_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5350_);
        v___x_5355_ = lean_box(1);
        v___x_5356_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5356_, 0, v___x_5355_);
        lean_ctor_set(v___x_5356_, 1, v_a_5352_);
        return v___x_5356_;
    } else {
        let mut v_quotContext_5357_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5358_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_5359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5364_: u8 = 0;
        let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_5357_ = lean_ctor_get(v_a_5351_, 1);
        v_currMacroScope_5358_ = lean_ctor_get(v_a_5351_, 2);
        v_ref_5359_ = lean_ctor_get(v_a_5351_, 5);
        v___x_5360_ = lean_unsigned_to_nat(0);
        v___x_5361_ = l_Lean_Syntax_getArg(v_x_5350_, v___x_5360_);
        v___x_5362_ = lean_unsigned_to_nat(2);
        v___x_5363_ = l_Lean_Syntax_getArg(v_x_5350_, v___x_5362_);
        lean_dec(v_x_5350_);
        v___x_5364_ = 0;
        v___x_5365_ = l_Lean_SourceInfo_fromRef(v_ref_5359_, v___x_5364_);
        v___x_5366_ = l___aux__Init__Core______macroRules__term___u2260____2___closed__1;
        v___x_5367_ = l___aux__Init__Core______macroRules__term___u2260____2___closed__2;
        lean_inc_n(v___x_5365_, 2);
        v___x_5368_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5368_, 0, v___x_5365_);
        lean_ctor_set(v___x_5368_, 1, v___x_5367_);
        v___x_5369_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2260____1___closed__1
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once
            ),
            _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1,
        );
        v___x_5370_ = l___aux__Init__Core______macroRules__term___u2260____1___closed__2;
        lean_inc(v_currMacroScope_5358_);
        lean_inc(v_quotContext_5357_);
        v___x_5371_ =
            l_Lean_addMacroScope(v_quotContext_5357_, v___x_5370_, v_currMacroScope_5358_);
        v___x_5372_ = l___aux__Init__Core______macroRules__term___u2260____1___closed__4;
        v___x_5373_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_5373_, 0, v___x_5365_);
        lean_ctor_set(v___x_5373_, 1, v___x_5369_);
        lean_ctor_set(v___x_5373_, 2, v___x_5371_);
        lean_ctor_set(v___x_5373_, 3, v___x_5372_);
        v___x_5374_ = l_Lean_Syntax_node4(
            v___x_5365_,
            v___x_5366_,
            v___x_5368_,
            v___x_5373_,
            v___x_5361_,
            v___x_5363_,
        );
        v___x_5375_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5375_, 0, v___x_5374_);
        lean_ctor_set(v___x_5375_, 1, v_a_5352_);
        return v___x_5375_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__term___u2260____2___boxed(
    mut v_x_5376_: *mut LeanObject,
    mut v_a_5377_: *mut LeanObject,
    mut v_a_5378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5379_: *mut LeanObject = core::ptr::null_mut();
    v_res_5379_ =
        l___aux__Init__Core______macroRules__term___u2260____2(v_x_5376_, v_a_5377_, v_a_5378_);
    lean_dec_ref(v_a_5377_);
    return v_res_5379_;
}
pub unsafe fn _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6()
-> *mut LeanObject {
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    v___x_5394_ =
        l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5;
    v___x_5395_ = l_String_toRawSubstring_x27(v___x_5394_);
    return v___x_5395_;
}
pub unsafe fn l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(
    mut v_x_5406_: *mut LeanObject,
    mut v_a_5407_: *mut LeanObject,
    mut v_a_5408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: u8 = 0;
    v___x_5409_ =
        l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2;
    v___x_5410_ = l_Lean_Syntax_isOfKind(v_x_5406_, v___x_5409_);
    if v___x_5410_ == 0 {
        let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
        v___x_5411_ = lean_box(1);
        v___x_5412_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5412_, 0, v___x_5411_);
        lean_ctor_set(v___x_5412_, 1, v_a_5408_);
        return v___x_5412_;
    } else {
        let mut v_quotContext_5413_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5414_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_5415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5416_: u8 = 0;
        let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_5413_ = lean_ctor_get(v_a_5407_, 1);
        v_currMacroScope_5414_ = lean_ctor_get(v_a_5407_, 2);
        v_ref_5415_ = lean_ctor_get(v_a_5407_, 5);
        v___x_5416_ = 0;
        v___x_5417_ = l_Lean_SourceInfo_fromRef(v_ref_5415_, v___x_5416_);
        v___x_5418_ =
            l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3;
        v___x_5419_ =
            l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4;
        lean_inc_n(v___x_5417_, 2);
        v___x_5420_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5420_, 0, v___x_5417_);
        lean_ctor_set(v___x_5420_, 1, v___x_5418_);
        v___x_5421_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6), core::ptr::addr_of_mut!(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6_once), _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6);
        v___x_5422_ =
            l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8;
        lean_inc(v_currMacroScope_5414_);
        lean_inc(v_quotContext_5413_);
        v___x_5423_ =
            l_Lean_addMacroScope(v_quotContext_5413_, v___x_5422_, v_currMacroScope_5414_);
        v___x_5424_ =
            l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10;
        v___x_5425_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_5425_, 0, v___x_5417_);
        lean_ctor_set(v___x_5425_, 1, v___x_5421_);
        lean_ctor_set(v___x_5425_, 2, v___x_5423_);
        lean_ctor_set(v___x_5425_, 3, v___x_5424_);
        v___x_5426_ = l_Lean_Syntax_node2(v___x_5417_, v___x_5419_, v___x_5420_, v___x_5425_);
        v___x_5427_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5427_, 0, v___x_5426_);
        lean_ctor_set(v___x_5427_, 1, v_a_5408_);
        return v___x_5427_;
    }
}
pub unsafe fn l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___boxed(
    mut v_x_5428_: *mut LeanObject,
    mut v_a_5429_: *mut LeanObject,
    mut v_a_5430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5431_: *mut LeanObject = core::ptr::null_mut();
    v_res_5431_ = l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(
        v_x_5428_, v_a_5429_, v_a_5430_,
    );
    lean_dec_ref(v_a_5429_);
    return v_res_5431_;
}
pub unsafe fn _init_l_instTransIff() -> *mut LeanObject {
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    v___x_5432_ = lean_box(0);
    return v___x_5432_;
}
pub unsafe fn l_toBoolUsing___redArg(mut v_d_5433_: u8) -> u8 {
    return v_d_5433_;
}
pub unsafe fn l_toBoolUsing___redArg___boxed(mut v_d_5434_: *mut LeanObject) -> *mut LeanObject {
    let mut v_d_boxed_5435_: u8 = 0;
    let mut v_res_5436_: u8 = 0;
    let mut v_r_5437_: *mut LeanObject = core::ptr::null_mut();
    v_d_boxed_5435_ = (lean_unbox(v_d_5434_) as u8);
    v_res_5436_ = l_toBoolUsing___redArg(v_d_boxed_5435_);
    v_r_5437_ = lean_box((v_res_5436_) as usize);
    return v_r_5437_;
}
pub unsafe fn l_toBoolUsing(mut v_p_5438_: *mut LeanObject, mut v_d_5439_: u8) -> u8 {
    return v_d_5439_;
}
pub unsafe fn l_toBoolUsing___boxed(
    mut v_p_5440_: *mut LeanObject,
    mut v_d_5441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_boxed_5442_: u8 = 0;
    let mut v_res_5443_: u8 = 0;
    let mut v_r_5444_: *mut LeanObject = core::ptr::null_mut();
    v_d_boxed_5442_ = (lean_unbox(v_d_5441_) as u8);
    v_res_5443_ = l_toBoolUsing(v_p_5440_, v_d_boxed_5442_);
    v_r_5444_ = lean_box((v_res_5443_) as usize);
    return v_r_5444_;
}
pub unsafe fn _init_l_instDecidableTrue() -> u8 {
    let mut v___x_5445_: u8 = 0;
    v___x_5445_ = 1;
    return v___x_5445_;
}
pub unsafe fn _init_l_instDecidableFalse() -> u8 {
    let mut v___x_5446_: u8 = 0;
    v___x_5446_ = 0;
    return v___x_5446_;
}
pub unsafe fn l_decidable__of__decidable__of__iff___redArg(mut v_inst_5447_: u8) -> u8 {
    return v_inst_5447_;
}
pub unsafe fn l_decidable__of__decidable__of__iff___redArg___boxed(
    mut v_inst_5448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_8__boxed_5449_: u8 = 0;
    let mut v_res_5450_: u8 = 0;
    let mut v_r_5451_: *mut LeanObject = core::ptr::null_mut();
    v_inst_8__boxed_5449_ = (lean_unbox(v_inst_5448_) as u8);
    v_res_5450_ = l_decidable__of__decidable__of__iff___redArg(v_inst_8__boxed_5449_);
    v_r_5451_ = lean_box((v_res_5450_) as usize);
    return v_r_5451_;
}
pub unsafe fn l_decidable__of__decidable__of__iff(
    mut v_p_5452_: *mut LeanObject,
    mut v_q_5453_: *mut LeanObject,
    mut v_inst_5454_: u8,
    mut v_h_5455_: *mut LeanObject,
) -> u8 {
    return v_inst_5454_;
}
pub unsafe fn l_decidable__of__decidable__of__iff___boxed(
    mut v_p_5456_: *mut LeanObject,
    mut v_q_5457_: *mut LeanObject,
    mut v_inst_5458_: *mut LeanObject,
    mut v_h_5459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_11__boxed_5460_: u8 = 0;
    let mut v_res_5461_: u8 = 0;
    let mut v_r_5462_: *mut LeanObject = core::ptr::null_mut();
    v_inst_11__boxed_5460_ = (lean_unbox(v_inst_5458_) as u8);
    v_res_5461_ = l_decidable__of__decidable__of__iff(
        v_p_5456_,
        v_q_5457_,
        v_inst_11__boxed_5460_,
        v_h_5459_,
    );
    v_r_5462_ = lean_box((v_res_5461_) as usize);
    return v_r_5462_;
}
pub unsafe fn l_decidable__of__decidable__of__eq___redArg(mut v_inst_5463_: u8) -> u8 {
    return v_inst_5463_;
}
pub unsafe fn l_decidable__of__decidable__of__eq___redArg___boxed(
    mut v_inst_5464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_8__boxed_5465_: u8 = 0;
    let mut v_res_5466_: u8 = 0;
    let mut v_r_5467_: *mut LeanObject = core::ptr::null_mut();
    v_inst_8__boxed_5465_ = (lean_unbox(v_inst_5464_) as u8);
    v_res_5466_ = l_decidable__of__decidable__of__eq___redArg(v_inst_8__boxed_5465_);
    v_r_5467_ = lean_box((v_res_5466_) as usize);
    return v_r_5467_;
}
pub unsafe fn l_decidable__of__decidable__of__eq(
    mut v_p_5468_: *mut LeanObject,
    mut v_q_5469_: *mut LeanObject,
    mut v_inst_5470_: u8,
    mut v_h_5471_: *mut LeanObject,
) -> u8 {
    return v_inst_5470_;
}
pub unsafe fn l_decidable__of__decidable__of__eq___boxed(
    mut v_p_5472_: *mut LeanObject,
    mut v_q_5473_: *mut LeanObject,
    mut v_inst_5474_: *mut LeanObject,
    mut v_h_5475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_11__boxed_5476_: u8 = 0;
    let mut v_res_5477_: u8 = 0;
    let mut v_r_5478_: *mut LeanObject = core::ptr::null_mut();
    v_inst_11__boxed_5476_ = (lean_unbox(v_inst_5474_) as u8);
    v_res_5477_ =
        l_decidable__of__decidable__of__eq(v_p_5472_, v_q_5473_, v_inst_11__boxed_5476_, v_h_5475_);
    v_r_5478_ = lean_box((v_res_5477_) as usize);
    return v_r_5478_;
}
pub unsafe fn l_instDecidableIff___redArg(mut v_inst_5479_: u8, mut v_inst_5480_: u8) -> u8 {
    if v_inst_5479_ == 0 {
        if v_inst_5480_ == 0 {
            let mut v___x_5481_: u8 = 0;
            v___x_5481_ = 1;
            return v___x_5481_;
        } else {
            return v_inst_5479_;
        }
    } else {
        return v_inst_5480_;
    }
}
pub unsafe fn l_instDecidableIff___redArg___boxed(
    mut v_inst_5482_: *mut LeanObject,
    mut v_inst_5483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_15__boxed_5484_: u8 = 0;
    let mut v_inst_16__boxed_5485_: u8 = 0;
    let mut v_res_5486_: u8 = 0;
    let mut v_r_5487_: *mut LeanObject = core::ptr::null_mut();
    v_inst_15__boxed_5484_ = (lean_unbox(v_inst_5482_) as u8);
    v_inst_16__boxed_5485_ = (lean_unbox(v_inst_5483_) as u8);
    v_res_5486_ = l_instDecidableIff___redArg(v_inst_15__boxed_5484_, v_inst_16__boxed_5485_);
    v_r_5487_ = lean_box((v_res_5486_) as usize);
    return v_r_5487_;
}
pub unsafe fn l_instDecidableIff(
    mut v_p_5488_: *mut LeanObject,
    mut v_q_5489_: *mut LeanObject,
    mut v_inst_5490_: u8,
    mut v_inst_5491_: u8,
) -> u8 {
    if v_inst_5490_ == 0 {
        if v_inst_5491_ == 0 {
            let mut v___x_5492_: u8 = 0;
            v___x_5492_ = 1;
            return v___x_5492_;
        } else {
            return v_inst_5490_;
        }
    } else {
        return v_inst_5491_;
    }
}
pub unsafe fn l_instDecidableIff___boxed(
    mut v_p_5493_: *mut LeanObject,
    mut v_q_5494_: *mut LeanObject,
    mut v_inst_5495_: *mut LeanObject,
    mut v_inst_5496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_23__boxed_5497_: u8 = 0;
    let mut v_inst_24__boxed_5498_: u8 = 0;
    let mut v_res_5499_: u8 = 0;
    let mut v_r_5500_: *mut LeanObject = core::ptr::null_mut();
    v_inst_23__boxed_5497_ = (lean_unbox(v_inst_5495_) as u8);
    v_inst_24__boxed_5498_ = (lean_unbox(v_inst_5496_) as u8);
    v_res_5499_ = l_instDecidableIff(
        v_p_5493_,
        v_q_5494_,
        v_inst_23__boxed_5497_,
        v_inst_24__boxed_5498_,
    );
    v_r_5500_ = lean_box((v_res_5499_) as usize);
    return v_r_5500_;
}
pub unsafe fn l_iteInduction___redArg(
    mut v_inst_5501_: u8,
    mut v_hpos_5502_: *mut LeanObject,
    mut v_hneg_5503_: *mut LeanObject,
) -> *mut LeanObject {
    if v_inst_5501_ == 0 {
        let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_hpos_5502_);
        v___x_5504_ = lean_apply_1(v_hneg_5503_, lean_box(0));
        return v___x_5504_;
    } else {
        let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_hneg_5503_);
        v___x_5505_ = lean_apply_1(v_hpos_5502_, lean_box(0));
        return v___x_5505_;
    }
}
pub unsafe fn l_iteInduction___redArg___boxed(
    mut v_inst_5506_: *mut LeanObject,
    mut v_hpos_5507_: *mut LeanObject,
    mut v_hneg_5508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_boxed_5509_: u8 = 0;
    let mut v_res_5510_: *mut LeanObject = core::ptr::null_mut();
    v_inst_boxed_5509_ = (lean_unbox(v_inst_5506_) as u8);
    v_res_5510_ = l_iteInduction___redArg(v_inst_boxed_5509_, v_hpos_5507_, v_hneg_5508_);
    return v_res_5510_;
}
pub unsafe fn l_iteInduction(
    mut v_00_u03b1_5511_: *mut LeanObject,
    mut v_c_5512_: *mut LeanObject,
    mut v_inst_5513_: u8,
    mut v_motive_5514_: *mut LeanObject,
    mut v_t_5515_: *mut LeanObject,
    mut v_e_5516_: *mut LeanObject,
    mut v_hpos_5517_: *mut LeanObject,
    mut v_hneg_5518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    v___x_5519_ = l_iteInduction___redArg(v_inst_5513_, v_hpos_5517_, v_hneg_5518_);
    return v___x_5519_;
}
pub unsafe fn l_iteInduction___boxed(
    mut v_00_u03b1_5520_: *mut LeanObject,
    mut v_c_5521_: *mut LeanObject,
    mut v_inst_5522_: *mut LeanObject,
    mut v_motive_5523_: *mut LeanObject,
    mut v_t_5524_: *mut LeanObject,
    mut v_e_5525_: *mut LeanObject,
    mut v_hpos_5526_: *mut LeanObject,
    mut v_hneg_5527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_boxed_5528_: u8 = 0;
    let mut v_res_5529_: *mut LeanObject = core::ptr::null_mut();
    v_inst_boxed_5528_ = (lean_unbox(v_inst_5522_) as u8);
    v_res_5529_ = l_iteInduction(
        v_00_u03b1_5520_,
        v_c_5521_,
        v_inst_boxed_5528_,
        v_motive_5523_,
        v_t_5524_,
        v_e_5525_,
        v_hpos_5526_,
        v_hneg_5527_,
    );
    lean_dec(v_e_5525_);
    lean_dec(v_t_5524_);
    return v_res_5529_;
}
pub unsafe fn l_instDecidableDite___redArg(
    mut v_dC_5530_: u8,
    mut v_dT_5531_: *mut LeanObject,
    mut v_dE_5532_: *mut LeanObject,
) -> u8 {
    if v_dC_5530_ == 0 {
        let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5534_: u8 = 0;
        lean_dec_ref(v_dT_5531_);
        v___x_5533_ = lean_apply_1(v_dE_5532_, lean_box(0));
        v___x_5534_ = (lean_unbox(v___x_5533_) as u8);
        return v___x_5534_;
    } else {
        let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5536_: u8 = 0;
        lean_dec_ref(v_dE_5532_);
        v___x_5535_ = lean_apply_1(v_dT_5531_, lean_box(0));
        v___x_5536_ = (lean_unbox(v___x_5535_) as u8);
        return v___x_5536_;
    }
}
pub unsafe fn l_instDecidableDite___redArg___boxed(
    mut v_dC_5537_: *mut LeanObject,
    mut v_dT_5538_: *mut LeanObject,
    mut v_dE_5539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dC_boxed_5540_: u8 = 0;
    let mut v_res_5541_: u8 = 0;
    let mut v_r_5542_: *mut LeanObject = core::ptr::null_mut();
    v_dC_boxed_5540_ = (lean_unbox(v_dC_5537_) as u8);
    v_res_5541_ = l_instDecidableDite___redArg(v_dC_boxed_5540_, v_dT_5538_, v_dE_5539_);
    v_r_5542_ = lean_box((v_res_5541_) as usize);
    return v_r_5542_;
}
pub unsafe fn l_instDecidableDite(
    mut v_c_5543_: *mut LeanObject,
    mut v_t_5544_: *mut LeanObject,
    mut v_e_5545_: *mut LeanObject,
    mut v_dC_5546_: u8,
    mut v_dT_5547_: *mut LeanObject,
    mut v_dE_5548_: *mut LeanObject,
) -> u8 {
    if v_dC_5546_ == 0 {
        let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5550_: u8 = 0;
        lean_dec_ref(v_dT_5547_);
        v___x_5549_ = lean_apply_1(v_dE_5548_, lean_box(0));
        v___x_5550_ = (lean_unbox(v___x_5549_) as u8);
        return v___x_5550_;
    } else {
        let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5552_: u8 = 0;
        lean_dec_ref(v_dE_5548_);
        v___x_5551_ = lean_apply_1(v_dT_5547_, lean_box(0));
        v___x_5552_ = (lean_unbox(v___x_5551_) as u8);
        return v___x_5552_;
    }
}
pub unsafe fn l_instDecidableDite___boxed(
    mut v_c_5553_: *mut LeanObject,
    mut v_t_5554_: *mut LeanObject,
    mut v_e_5555_: *mut LeanObject,
    mut v_dC_5556_: *mut LeanObject,
    mut v_dT_5557_: *mut LeanObject,
    mut v_dE_5558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dC_boxed_5559_: u8 = 0;
    let mut v_res_5560_: u8 = 0;
    let mut v_r_5561_: *mut LeanObject = core::ptr::null_mut();
    v_dC_boxed_5559_ = (lean_unbox(v_dC_5556_) as u8);
    v_res_5560_ = l_instDecidableDite(
        v_c_5553_,
        v_t_5554_,
        v_e_5555_,
        v_dC_boxed_5559_,
        v_dT_5557_,
        v_dE_5558_,
    );
    v_r_5561_ = lean_box((v_res_5560_) as usize);
    return v_r_5561_;
}
pub unsafe fn l_noConfusionEnum___redArg___lam__0(
    mut v_x_5562_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_5562_);
    return v_x_5562_;
}
pub unsafe fn l_noConfusionEnum___redArg___lam__0___boxed(
    mut v_x_5563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5564_: *mut LeanObject = core::ptr::null_mut();
    v_res_5564_ = l_noConfusionEnum___redArg___lam__0(v_x_5563_);
    lean_dec(v_x_5563_);
    return v_res_5564_;
}
pub unsafe fn l_noConfusionEnum___redArg(
    mut v_inst_5566_: *mut LeanObject,
    mut v_f_5567_: *mut LeanObject,
    mut v_x_5568_: *mut LeanObject,
    mut v_y_5569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5573_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_f_5567_);
    v___x_5570_ = lean_apply_1(v_f_5567_, v_x_5568_);
    v___x_5571_ = lean_apply_1(v_f_5567_, v_y_5569_);
    v___x_5572_ = lean_apply_2(v_inst_5566_, v___x_5570_, v___x_5571_);
    v___f_5573_ = l_noConfusionEnum___redArg___closed__0;
    return v___f_5573_;
}
pub unsafe fn l_noConfusionEnum(
    mut v_00_u03b1_5574_: *mut LeanObject,
    mut v_00_u03b2_5575_: *mut LeanObject,
    mut v_inst_5576_: *mut LeanObject,
    mut v_f_5577_: *mut LeanObject,
    mut v_P_5578_: *mut LeanObject,
    mut v_x_5579_: *mut LeanObject,
    mut v_y_5580_: *mut LeanObject,
    mut v_h_5581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5585_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_f_5577_);
    v___x_5582_ = lean_apply_1(v_f_5577_, v_x_5579_);
    v___x_5583_ = lean_apply_1(v_f_5577_, v_y_5580_);
    v___x_5584_ = lean_apply_2(v_inst_5576_, v___x_5582_, v___x_5583_);
    v___f_5585_ = l_noConfusionEnum___redArg___closed__0;
    return v___f_5585_;
}
pub unsafe fn _init_l_instInhabitedProp() -> *mut LeanObject {
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    v___x_5586_ = lean_box(0);
    return v___x_5586_;
}
pub unsafe fn _init_l_instInhabitedNonScalar_default() -> *mut LeanObject {
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    v___x_5587_ = lean_unsigned_to_nat(0);
    return v___x_5587_;
}
pub unsafe fn _init_l_instInhabitedNonScalar() -> *mut LeanObject {
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    v___x_5588_ = lean_unsigned_to_nat(0);
    return v___x_5588_;
}
pub unsafe fn _init_l_instInhabitedPNonScalar_default() -> *mut LeanObject {
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    v___x_5589_ = lean_unsigned_to_nat(0);
    return v___x_5589_;
}
pub unsafe fn _init_l_instInhabitedPNonScalar() -> *mut LeanObject {
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    v___x_5590_ = lean_unsigned_to_nat(0);
    return v___x_5590_;
}
pub unsafe fn _init_l_instInhabitedTrue() -> *mut LeanObject {
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    v___x_5591_ = lean_box(0);
    return v___x_5591_;
}
pub unsafe fn l_Subtype_instBEq___redArg___lam__0(
    mut v_inst_5592_: *mut LeanObject,
    mut v_x_5593_: *mut LeanObject,
    mut v_y_5594_: *mut LeanObject,
) -> u8 {
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: u8 = 0;
    v___x_5595_ = lean_apply_2(v_inst_5592_, v_x_5593_, v_y_5594_);
    v___x_5596_ = (lean_unbox(v___x_5595_) as u8);
    return v___x_5596_;
}
pub unsafe fn l_Subtype_instBEq___redArg___lam__0___boxed(
    mut v_inst_5597_: *mut LeanObject,
    mut v_x_5598_: *mut LeanObject,
    mut v_y_5599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5600_: u8 = 0;
    let mut v_r_5601_: *mut LeanObject = core::ptr::null_mut();
    v_res_5600_ = l_Subtype_instBEq___redArg___lam__0(v_inst_5597_, v_x_5598_, v_y_5599_);
    v_r_5601_ = lean_box((v_res_5600_) as usize);
    return v_r_5601_;
}
pub unsafe fn l_Subtype_instBEq___redArg(mut v_inst_5602_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5603_: *mut LeanObject = core::ptr::null_mut();
    v___f_5603_ = lean_alloc_closure(
        l_Subtype_instBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5603_, 0, v_inst_5602_);
    return v___f_5603_;
}
pub unsafe fn l_Subtype_instBEq(
    mut v_00_u03b1_5604_: *mut LeanObject,
    mut v_p_5605_: *mut LeanObject,
    mut v_inst_5606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5607_: *mut LeanObject = core::ptr::null_mut();
    v___f_5607_ = lean_alloc_closure(
        l_Subtype_instBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5607_, 0, v_inst_5606_);
    return v___f_5607_;
}
pub unsafe fn l_Subtype_instDecidableEq___redArg(
    mut v_inst_5608_: *mut LeanObject,
    mut v_x_5609_: *mut LeanObject,
    mut v_x_5610_: *mut LeanObject,
) -> u8 {
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: u8 = 0;
    v___x_5611_ = lean_apply_2(v_inst_5608_, v_x_5609_, v_x_5610_);
    v___x_5612_ = (lean_unbox(v___x_5611_) as u8);
    return v___x_5612_;
}
pub unsafe fn l_Subtype_instDecidableEq___redArg___boxed(
    mut v_inst_5613_: *mut LeanObject,
    mut v_x_5614_: *mut LeanObject,
    mut v_x_5615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5616_: u8 = 0;
    let mut v_r_5617_: *mut LeanObject = core::ptr::null_mut();
    v_res_5616_ = l_Subtype_instDecidableEq___redArg(v_inst_5613_, v_x_5614_, v_x_5615_);
    v_r_5617_ = lean_box((v_res_5616_) as usize);
    return v_r_5617_;
}
pub unsafe fn l_Subtype_instDecidableEq(
    mut v_00_u03b1_5618_: *mut LeanObject,
    mut v_p_5619_: *mut LeanObject,
    mut v_inst_5620_: *mut LeanObject,
    mut v_x_5621_: *mut LeanObject,
    mut v_x_5622_: *mut LeanObject,
) -> u8 {
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: u8 = 0;
    v___x_5623_ = lean_apply_2(v_inst_5620_, v_x_5621_, v_x_5622_);
    v___x_5624_ = (lean_unbox(v___x_5623_) as u8);
    return v___x_5624_;
}
pub unsafe fn l_Subtype_instDecidableEq___boxed(
    mut v_00_u03b1_5625_: *mut LeanObject,
    mut v_p_5626_: *mut LeanObject,
    mut v_inst_5627_: *mut LeanObject,
    mut v_x_5628_: *mut LeanObject,
    mut v_x_5629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5630_: u8 = 0;
    let mut v_r_5631_: *mut LeanObject = core::ptr::null_mut();
    v_res_5630_ = l_Subtype_instDecidableEq(
        v_00_u03b1_5625_,
        v_p_5626_,
        v_inst_5627_,
        v_x_5628_,
        v_x_5629_,
    );
    v_r_5631_ = lean_box((v_res_5630_) as usize);
    return v_r_5631_;
}
pub unsafe fn l_Sum_inhabitedLeft___redArg(mut v_inst_5632_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    v___x_5633_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5633_, 0, v_inst_5632_);
    return v___x_5633_;
}
pub unsafe fn l_Sum_inhabitedLeft(
    mut v_00_u03b1_5634_: *mut LeanObject,
    mut v_00_u03b2_5635_: *mut LeanObject,
    mut v_inst_5636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    v___x_5637_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5637_, 0, v_inst_5636_);
    return v___x_5637_;
}
pub unsafe fn l_Sum_inhabitedRight___redArg(mut v_inst_5638_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    v___x_5639_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5639_, 0, v_inst_5638_);
    return v___x_5639_;
}
pub unsafe fn l_Sum_inhabitedRight(
    mut v_00_u03b1_5640_: *mut LeanObject,
    mut v_00_u03b2_5641_: *mut LeanObject,
    mut v_inst_5642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    v___x_5643_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5643_, 0, v_inst_5642_);
    return v___x_5643_;
}
pub unsafe fn l_instDecidableEqSum_decEq___redArg(
    mut v_inst_5644_: *mut LeanObject,
    mut v_inst_5645_: *mut LeanObject,
    mut v_x_5646_: *mut LeanObject,
    mut v_x_5647_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_5646_) == 0 {
        lean_dec_ref(v_inst_5645_);
        if lean_obj_tag(v_x_5647_) == 0 {
            let mut v_val_5648_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_5649_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5651_: u8 = 0;
            v_val_5648_ = lean_ctor_get(v_x_5646_, 0);
            lean_inc(v_val_5648_);
            lean_dec_ref_known(v_x_5646_, 1);
            v_val_5649_ = lean_ctor_get(v_x_5647_, 0);
            lean_inc(v_val_5649_);
            lean_dec_ref_known(v_x_5647_, 1);
            v___x_5650_ = lean_apply_2(v_inst_5644_, v_val_5648_, v_val_5649_);
            v___x_5651_ = (lean_unbox(v___x_5650_) as u8);
            return v___x_5651_;
        } else {
            let mut v___x_5652_: u8 = 0;
            lean_dec_ref_known(v_x_5647_, 1);
            lean_dec_ref_known(v_x_5646_, 1);
            lean_dec_ref(v_inst_5644_);
            v___x_5652_ = 0;
            return v___x_5652_;
        }
    } else {
        lean_dec_ref(v_inst_5644_);
        if lean_obj_tag(v_x_5647_) == 0 {
            let mut v___x_5653_: u8 = 0;
            lean_dec_ref_known(v_x_5647_, 1);
            lean_dec_ref_known(v_x_5646_, 1);
            lean_dec_ref(v_inst_5645_);
            v___x_5653_ = 0;
            return v___x_5653_;
        } else {
            let mut v_val_5654_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_5655_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5657_: u8 = 0;
            v_val_5654_ = lean_ctor_get(v_x_5646_, 0);
            lean_inc(v_val_5654_);
            lean_dec_ref_known(v_x_5646_, 1);
            v_val_5655_ = lean_ctor_get(v_x_5647_, 0);
            lean_inc(v_val_5655_);
            lean_dec_ref_known(v_x_5647_, 1);
            v___x_5656_ = lean_apply_2(v_inst_5645_, v_val_5654_, v_val_5655_);
            v___x_5657_ = (lean_unbox(v___x_5656_) as u8);
            return v___x_5657_;
        }
    }
}
pub unsafe fn l_instDecidableEqSum_decEq___redArg___boxed(
    mut v_inst_5658_: *mut LeanObject,
    mut v_inst_5659_: *mut LeanObject,
    mut v_x_5660_: *mut LeanObject,
    mut v_x_5661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5662_: u8 = 0;
    let mut v_r_5663_: *mut LeanObject = core::ptr::null_mut();
    v_res_5662_ =
        l_instDecidableEqSum_decEq___redArg(v_inst_5658_, v_inst_5659_, v_x_5660_, v_x_5661_);
    v_r_5663_ = lean_box((v_res_5662_) as usize);
    return v_r_5663_;
}
pub unsafe fn l_instDecidableEqSum_decEq(
    mut v_00_u03b1_5664_: *mut LeanObject,
    mut v_00_u03b2_5665_: *mut LeanObject,
    mut v_inst_5666_: *mut LeanObject,
    mut v_inst_5667_: *mut LeanObject,
    mut v_x_5668_: *mut LeanObject,
    mut v_x_5669_: *mut LeanObject,
) -> u8 {
    let mut v___x_5670_: u8 = 0;
    v___x_5670_ =
        l_instDecidableEqSum_decEq___redArg(v_inst_5666_, v_inst_5667_, v_x_5668_, v_x_5669_);
    return v___x_5670_;
}
pub unsafe fn l_instDecidableEqSum_decEq___boxed(
    mut v_00_u03b1_5671_: *mut LeanObject,
    mut v_00_u03b2_5672_: *mut LeanObject,
    mut v_inst_5673_: *mut LeanObject,
    mut v_inst_5674_: *mut LeanObject,
    mut v_x_5675_: *mut LeanObject,
    mut v_x_5676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5677_: u8 = 0;
    let mut v_r_5678_: *mut LeanObject = core::ptr::null_mut();
    v_res_5677_ = l_instDecidableEqSum_decEq(
        v_00_u03b1_5671_,
        v_00_u03b2_5672_,
        v_inst_5673_,
        v_inst_5674_,
        v_x_5675_,
        v_x_5676_,
    );
    v_r_5678_ = lean_box((v_res_5677_) as usize);
    return v_r_5678_;
}
pub unsafe fn l_instDecidableEqSum___redArg(
    mut v_inst_5679_: *mut LeanObject,
    mut v_inst_5680_: *mut LeanObject,
    mut v_x_5681_: *mut LeanObject,
    mut v_x_5682_: *mut LeanObject,
) -> u8 {
    let mut v___x_5683_: u8 = 0;
    v___x_5683_ =
        l_instDecidableEqSum_decEq___redArg(v_inst_5679_, v_inst_5680_, v_x_5681_, v_x_5682_);
    return v___x_5683_;
}
pub unsafe fn l_instDecidableEqSum___redArg___boxed(
    mut v_inst_5684_: *mut LeanObject,
    mut v_inst_5685_: *mut LeanObject,
    mut v_x_5686_: *mut LeanObject,
    mut v_x_5687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5688_: u8 = 0;
    let mut v_r_5689_: *mut LeanObject = core::ptr::null_mut();
    v_res_5688_ = l_instDecidableEqSum___redArg(v_inst_5684_, v_inst_5685_, v_x_5686_, v_x_5687_);
    v_r_5689_ = lean_box((v_res_5688_) as usize);
    return v_r_5689_;
}
pub unsafe fn l_instDecidableEqSum(
    mut v_00_u03b1_5690_: *mut LeanObject,
    mut v_00_u03b2_5691_: *mut LeanObject,
    mut v_inst_5692_: *mut LeanObject,
    mut v_inst_5693_: *mut LeanObject,
    mut v_x_5694_: *mut LeanObject,
    mut v_x_5695_: *mut LeanObject,
) -> u8 {
    let mut v___x_5696_: u8 = 0;
    v___x_5696_ =
        l_instDecidableEqSum_decEq___redArg(v_inst_5692_, v_inst_5693_, v_x_5694_, v_x_5695_);
    return v___x_5696_;
}
pub unsafe fn l_instDecidableEqSum___boxed(
    mut v_00_u03b1_5697_: *mut LeanObject,
    mut v_00_u03b2_5698_: *mut LeanObject,
    mut v_inst_5699_: *mut LeanObject,
    mut v_inst_5700_: *mut LeanObject,
    mut v_x_5701_: *mut LeanObject,
    mut v_x_5702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5703_: u8 = 0;
    let mut v_r_5704_: *mut LeanObject = core::ptr::null_mut();
    v_res_5703_ = l_instDecidableEqSum(
        v_00_u03b1_5697_,
        v_00_u03b2_5698_,
        v_inst_5699_,
        v_inst_5700_,
        v_x_5701_,
        v_x_5702_,
    );
    v_r_5704_ = lean_box((v_res_5703_) as usize);
    return v_r_5704_;
}
pub unsafe fn l_instInhabitedProd___redArg(
    mut v_inst_5705_: *mut LeanObject,
    mut v_inst_5706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    v___x_5707_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5707_, 0, v_inst_5705_);
    lean_ctor_set(v___x_5707_, 1, v_inst_5706_);
    return v___x_5707_;
}
pub unsafe fn l_instInhabitedProd(
    mut v_00_u03b1_5708_: *mut LeanObject,
    mut v_00_u03b2_5709_: *mut LeanObject,
    mut v_inst_5710_: *mut LeanObject,
    mut v_inst_5711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    v___x_5712_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5712_, 0, v_inst_5710_);
    lean_ctor_set(v___x_5712_, 1, v_inst_5711_);
    return v___x_5712_;
}
pub unsafe fn l_instInhabitedMProd___redArg(
    mut v_inst_5713_: *mut LeanObject,
    mut v_inst_5714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    v___x_5715_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5715_, 0, v_inst_5713_);
    lean_ctor_set(v___x_5715_, 1, v_inst_5714_);
    return v___x_5715_;
}
pub unsafe fn l_instInhabitedMProd(
    mut v_00_u03b1_5716_: *mut LeanObject,
    mut v_00_u03b2_5717_: *mut LeanObject,
    mut v_inst_5718_: *mut LeanObject,
    mut v_inst_5719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    v___x_5720_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5720_, 0, v_inst_5718_);
    lean_ctor_set(v___x_5720_, 1, v_inst_5719_);
    return v___x_5720_;
}
pub unsafe fn l_instInhabitedPProd___redArg(
    mut v_inst_5721_: *mut LeanObject,
    mut v_inst_5722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    v___x_5723_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5723_, 0, v_inst_5721_);
    lean_ctor_set(v___x_5723_, 1, v_inst_5722_);
    return v___x_5723_;
}
pub unsafe fn l_instInhabitedPProd(
    mut v_00_u03b1_5724_: *mut LeanObject,
    mut v_00_u03b2_5725_: *mut LeanObject,
    mut v_inst_5726_: *mut LeanObject,
    mut v_inst_5727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    v___x_5728_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5728_, 0, v_inst_5726_);
    lean_ctor_set(v___x_5728_, 1, v_inst_5727_);
    return v___x_5728_;
}
pub unsafe fn l_instDecidableEqProd___redArg(
    mut v_inst_5729_: *mut LeanObject,
    mut v_inst_5730_: *mut LeanObject,
    mut v_x_5731_: *mut LeanObject,
    mut v_x_5732_: *mut LeanObject,
) -> u8 {
    let mut v_fst_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: u8 = 0;
    v_fst_5733_ = lean_ctor_get(v_x_5731_, 0);
    lean_inc(v_fst_5733_);
    v_snd_5734_ = lean_ctor_get(v_x_5731_, 1);
    lean_inc(v_snd_5734_);
    lean_dec_ref(v_x_5731_);
    v_fst_5735_ = lean_ctor_get(v_x_5732_, 0);
    lean_inc(v_fst_5735_);
    v_snd_5736_ = lean_ctor_get(v_x_5732_, 1);
    lean_inc(v_snd_5736_);
    lean_dec_ref(v_x_5732_);
    v___x_5737_ = lean_apply_2(v_inst_5729_, v_fst_5733_, v_fst_5735_);
    v___x_5738_ = (lean_unbox(v___x_5737_) as u8);
    if v___x_5738_ == 0 {
        let mut v___x_5739_: u8 = 0;
        lean_dec(v_snd_5736_);
        lean_dec(v_snd_5734_);
        lean_dec_ref(v_inst_5730_);
        v___x_5739_ = (lean_unbox(v___x_5737_) as u8);
        return v___x_5739_;
    } else {
        let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5741_: u8 = 0;
        v___x_5740_ = lean_apply_2(v_inst_5730_, v_snd_5734_, v_snd_5736_);
        v___x_5741_ = (lean_unbox(v___x_5740_) as u8);
        return v___x_5741_;
    }
}
pub unsafe fn l_instDecidableEqProd___redArg___boxed(
    mut v_inst_5742_: *mut LeanObject,
    mut v_inst_5743_: *mut LeanObject,
    mut v_x_5744_: *mut LeanObject,
    mut v_x_5745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5746_: u8 = 0;
    let mut v_r_5747_: *mut LeanObject = core::ptr::null_mut();
    v_res_5746_ = l_instDecidableEqProd___redArg(v_inst_5742_, v_inst_5743_, v_x_5744_, v_x_5745_);
    v_r_5747_ = lean_box((v_res_5746_) as usize);
    return v_r_5747_;
}
pub unsafe fn l_instDecidableEqProd(
    mut v_00_u03b1_5748_: *mut LeanObject,
    mut v_00_u03b2_5749_: *mut LeanObject,
    mut v_inst_5750_: *mut LeanObject,
    mut v_inst_5751_: *mut LeanObject,
    mut v_x_5752_: *mut LeanObject,
    mut v_x_5753_: *mut LeanObject,
) -> u8 {
    let mut v___x_5754_: u8 = 0;
    v___x_5754_ = l_instDecidableEqProd___redArg(v_inst_5750_, v_inst_5751_, v_x_5752_, v_x_5753_);
    return v___x_5754_;
}
pub unsafe fn l_instDecidableEqProd___boxed(
    mut v_00_u03b1_5755_: *mut LeanObject,
    mut v_00_u03b2_5756_: *mut LeanObject,
    mut v_inst_5757_: *mut LeanObject,
    mut v_inst_5758_: *mut LeanObject,
    mut v_x_5759_: *mut LeanObject,
    mut v_x_5760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5761_: u8 = 0;
    let mut v_r_5762_: *mut LeanObject = core::ptr::null_mut();
    v_res_5761_ = l_instDecidableEqProd(
        v_00_u03b1_5755_,
        v_00_u03b2_5756_,
        v_inst_5757_,
        v_inst_5758_,
        v_x_5759_,
        v_x_5760_,
    );
    v_r_5762_ = lean_box((v_res_5761_) as usize);
    return v_r_5762_;
}
pub unsafe fn l_instBEqProd___redArg___lam__0(
    mut v_inst_5763_: *mut LeanObject,
    mut v_inst_5764_: *mut LeanObject,
    mut v_x_5765_: *mut LeanObject,
    mut v_x_5766_: *mut LeanObject,
) -> u8 {
    let mut v_fst_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: u8 = 0;
    v_fst_5767_ = lean_ctor_get(v_x_5765_, 0);
    lean_inc(v_fst_5767_);
    v_snd_5768_ = lean_ctor_get(v_x_5765_, 1);
    lean_inc(v_snd_5768_);
    lean_dec_ref(v_x_5765_);
    v_fst_5769_ = lean_ctor_get(v_x_5766_, 0);
    lean_inc(v_fst_5769_);
    v_snd_5770_ = lean_ctor_get(v_x_5766_, 1);
    lean_inc(v_snd_5770_);
    lean_dec_ref(v_x_5766_);
    v___x_5771_ = lean_apply_2(v_inst_5763_, v_fst_5767_, v_fst_5769_);
    v___x_5772_ = (lean_unbox(v___x_5771_) as u8);
    if v___x_5772_ == 0 {
        let mut v___x_5773_: u8 = 0;
        lean_dec(v_snd_5770_);
        lean_dec(v_snd_5768_);
        lean_dec_ref(v_inst_5764_);
        v___x_5773_ = (lean_unbox(v___x_5771_) as u8);
        return v___x_5773_;
    } else {
        let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5775_: u8 = 0;
        v___x_5774_ = lean_apply_2(v_inst_5764_, v_snd_5768_, v_snd_5770_);
        v___x_5775_ = (lean_unbox(v___x_5774_) as u8);
        return v___x_5775_;
    }
}
pub unsafe fn l_instBEqProd___redArg___lam__0___boxed(
    mut v_inst_5776_: *mut LeanObject,
    mut v_inst_5777_: *mut LeanObject,
    mut v_x_5778_: *mut LeanObject,
    mut v_x_5779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5780_: u8 = 0;
    let mut v_r_5781_: *mut LeanObject = core::ptr::null_mut();
    v_res_5780_ = l_instBEqProd___redArg___lam__0(v_inst_5776_, v_inst_5777_, v_x_5778_, v_x_5779_);
    v_r_5781_ = lean_box((v_res_5780_) as usize);
    return v_r_5781_;
}
pub unsafe fn l_instBEqProd___redArg(
    mut v_inst_5782_: *mut LeanObject,
    mut v_inst_5783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5784_: *mut LeanObject = core::ptr::null_mut();
    v___f_5784_ = lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_5784_, 0, v_inst_5782_);
    lean_closure_set(v___f_5784_, 1, v_inst_5783_);
    return v___f_5784_;
}
pub unsafe fn l_instBEqProd(
    mut v_00_u03b1_5785_: *mut LeanObject,
    mut v_00_u03b2_5786_: *mut LeanObject,
    mut v_inst_5787_: *mut LeanObject,
    mut v_inst_5788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5789_: *mut LeanObject = core::ptr::null_mut();
    v___f_5789_ = lean_alloc_closure(
        l_instBEqProd___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_5789_, 0, v_inst_5787_);
    lean_closure_set(v___f_5789_, 1, v_inst_5788_);
    return v___f_5789_;
}
pub unsafe fn l_Prod_lexLtDec___aux__1___redArg(
    mut v_inst_5790_: *mut LeanObject,
    mut v_inst_5791_: *mut LeanObject,
    mut v_inst_5792_: *mut LeanObject,
    mut v_x_5793_: *mut LeanObject,
    mut v_x_5794_: *mut LeanObject,
) -> u8 {
    let mut v_fst_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: u8 = 0;
    v_fst_5795_ = lean_ctor_get(v_x_5793_, 0);
    lean_inc_n(v_fst_5795_, 2);
    v_snd_5796_ = lean_ctor_get(v_x_5793_, 1);
    lean_inc(v_snd_5796_);
    lean_dec_ref(v_x_5793_);
    v_fst_5797_ = lean_ctor_get(v_x_5794_, 0);
    lean_inc_n(v_fst_5797_, 2);
    v_snd_5798_ = lean_ctor_get(v_x_5794_, 1);
    lean_inc(v_snd_5798_);
    lean_dec_ref(v_x_5794_);
    v___x_5799_ = lean_apply_2(v_inst_5791_, v_fst_5795_, v_fst_5797_);
    v___x_5800_ = (lean_unbox(v___x_5799_) as u8);
    if v___x_5800_ == 0 {
        let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5802_: u8 = 0;
        v___x_5801_ = lean_apply_2(v_inst_5790_, v_fst_5795_, v_fst_5797_);
        v___x_5802_ = (lean_unbox(v___x_5801_) as u8);
        if v___x_5802_ == 0 {
            let mut v___x_5803_: u8 = 0;
            lean_dec(v_snd_5798_);
            lean_dec(v_snd_5796_);
            lean_dec_ref(v_inst_5792_);
            v___x_5803_ = (lean_unbox(v___x_5801_) as u8);
            return v___x_5803_;
        } else {
            let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5805_: u8 = 0;
            v___x_5804_ = lean_apply_2(v_inst_5792_, v_snd_5796_, v_snd_5798_);
            v___x_5805_ = (lean_unbox(v___x_5804_) as u8);
            return v___x_5805_;
        }
    } else {
        let mut v___x_5806_: u8 = 0;
        lean_dec(v_snd_5798_);
        lean_dec(v_fst_5797_);
        lean_dec(v_snd_5796_);
        lean_dec(v_fst_5795_);
        lean_dec_ref(v_inst_5792_);
        lean_dec_ref(v_inst_5790_);
        v___x_5806_ = (lean_unbox(v___x_5799_) as u8);
        return v___x_5806_;
    }
}
pub unsafe fn l_Prod_lexLtDec___aux__1___redArg___boxed(
    mut v_inst_5807_: *mut LeanObject,
    mut v_inst_5808_: *mut LeanObject,
    mut v_inst_5809_: *mut LeanObject,
    mut v_x_5810_: *mut LeanObject,
    mut v_x_5811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5812_: u8 = 0;
    let mut v_r_5813_: *mut LeanObject = core::ptr::null_mut();
    v_res_5812_ = l_Prod_lexLtDec___aux__1___redArg(
        v_inst_5807_,
        v_inst_5808_,
        v_inst_5809_,
        v_x_5810_,
        v_x_5811_,
    );
    v_r_5813_ = lean_box((v_res_5812_) as usize);
    return v_r_5813_;
}
pub unsafe fn l_Prod_lexLtDec___aux__1(
    mut v_00_u03b1_5814_: *mut LeanObject,
    mut v_00_u03b2_5815_: *mut LeanObject,
    mut v_inst_5816_: *mut LeanObject,
    mut v_inst_5817_: *mut LeanObject,
    mut v_inst_5818_: *mut LeanObject,
    mut v_inst_5819_: *mut LeanObject,
    mut v_inst_5820_: *mut LeanObject,
    mut v_x_5821_: *mut LeanObject,
    mut v_x_5822_: *mut LeanObject,
) -> u8 {
    let mut v___x_5823_: u8 = 0;
    v___x_5823_ = l_Prod_lexLtDec___aux__1___redArg(
        v_inst_5818_,
        v_inst_5819_,
        v_inst_5820_,
        v_x_5821_,
        v_x_5822_,
    );
    return v___x_5823_;
}
pub unsafe fn l_Prod_lexLtDec___aux__1___boxed(
    mut v_00_u03b1_5824_: *mut LeanObject,
    mut v_00_u03b2_5825_: *mut LeanObject,
    mut v_inst_5826_: *mut LeanObject,
    mut v_inst_5827_: *mut LeanObject,
    mut v_inst_5828_: *mut LeanObject,
    mut v_inst_5829_: *mut LeanObject,
    mut v_inst_5830_: *mut LeanObject,
    mut v_x_5831_: *mut LeanObject,
    mut v_x_5832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5833_: u8 = 0;
    let mut v_r_5834_: *mut LeanObject = core::ptr::null_mut();
    v_res_5833_ = l_Prod_lexLtDec___aux__1(
        v_00_u03b1_5824_,
        v_00_u03b2_5825_,
        v_inst_5826_,
        v_inst_5827_,
        v_inst_5828_,
        v_inst_5829_,
        v_inst_5830_,
        v_x_5831_,
        v_x_5832_,
    );
    v_r_5834_ = lean_box((v_res_5833_) as usize);
    return v_r_5834_;
}
pub unsafe fn l_Prod_lexLtDec___redArg(
    mut v_inst_5835_: *mut LeanObject,
    mut v_inst_5836_: *mut LeanObject,
    mut v_inst_5837_: *mut LeanObject,
    mut v_x_5838_: *mut LeanObject,
    mut v_x_5839_: *mut LeanObject,
) -> u8 {
    let mut v___x_5840_: u8 = 0;
    v___x_5840_ = l_Prod_lexLtDec___aux__1___redArg(
        v_inst_5835_,
        v_inst_5836_,
        v_inst_5837_,
        v_x_5838_,
        v_x_5839_,
    );
    return v___x_5840_;
}
pub unsafe fn l_Prod_lexLtDec___redArg___boxed(
    mut v_inst_5841_: *mut LeanObject,
    mut v_inst_5842_: *mut LeanObject,
    mut v_inst_5843_: *mut LeanObject,
    mut v_x_5844_: *mut LeanObject,
    mut v_x_5845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5846_: u8 = 0;
    let mut v_r_5847_: *mut LeanObject = core::ptr::null_mut();
    v_res_5846_ = l_Prod_lexLtDec___redArg(
        v_inst_5841_,
        v_inst_5842_,
        v_inst_5843_,
        v_x_5844_,
        v_x_5845_,
    );
    v_r_5847_ = lean_box((v_res_5846_) as usize);
    return v_r_5847_;
}
pub unsafe fn l_Prod_lexLtDec(
    mut v_00_u03b1_5848_: *mut LeanObject,
    mut v_00_u03b2_5849_: *mut LeanObject,
    mut v_inst_5850_: *mut LeanObject,
    mut v_inst_5851_: *mut LeanObject,
    mut v_inst_5852_: *mut LeanObject,
    mut v_inst_5853_: *mut LeanObject,
    mut v_inst_5854_: *mut LeanObject,
    mut v_x_5855_: *mut LeanObject,
    mut v_x_5856_: *mut LeanObject,
) -> u8 {
    let mut v___x_5857_: u8 = 0;
    v___x_5857_ = l_Prod_lexLtDec___aux__1___redArg(
        v_inst_5852_,
        v_inst_5853_,
        v_inst_5854_,
        v_x_5855_,
        v_x_5856_,
    );
    return v___x_5857_;
}
pub unsafe fn l_Prod_lexLtDec___boxed(
    mut v_00_u03b1_5858_: *mut LeanObject,
    mut v_00_u03b2_5859_: *mut LeanObject,
    mut v_inst_5860_: *mut LeanObject,
    mut v_inst_5861_: *mut LeanObject,
    mut v_inst_5862_: *mut LeanObject,
    mut v_inst_5863_: *mut LeanObject,
    mut v_inst_5864_: *mut LeanObject,
    mut v_x_5865_: *mut LeanObject,
    mut v_x_5866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5867_: u8 = 0;
    let mut v_r_5868_: *mut LeanObject = core::ptr::null_mut();
    v_res_5867_ = l_Prod_lexLtDec(
        v_00_u03b1_5858_,
        v_00_u03b2_5859_,
        v_inst_5860_,
        v_inst_5861_,
        v_inst_5862_,
        v_inst_5863_,
        v_inst_5864_,
        v_x_5865_,
        v_x_5866_,
    );
    v_r_5868_ = lean_box((v_res_5867_) as usize);
    return v_r_5868_;
}
pub unsafe fn l_Prod_map___redArg(
    mut v_f_5869_: *mut LeanObject,
    mut v_g_5870_: *mut LeanObject,
    mut v_x_5871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5876_: u8 = 0;
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5872_ = lean_ctor_get(v_x_5871_, 0);
                v_snd_5873_ = lean_ctor_get(v_x_5871_, 1);
                v_isSharedCheck_5882_ = (!lean_is_exclusive(v_x_5871_)) as u8;
                if v_isSharedCheck_5882_ == 0 {
                    v___x_5875_ = v_x_5871_;
                    v_isShared_5876_ = v_isSharedCheck_5882_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_5873_);
                    lean_inc(v_fst_5872_);
                    lean_dec(v_x_5871_);
                    v___x_5875_ = lean_box(0);
                    v_isShared_5876_ = v_isSharedCheck_5882_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5877_ = lean_apply_1(v_f_5869_, v_fst_5872_);
                v___x_5878_ = lean_apply_1(v_g_5870_, v_snd_5873_);
                if v_isShared_5876_ == 0 {
                    lean_ctor_set(v___x_5875_, 1, v___x_5878_);
                    lean_ctor_set(v___x_5875_, 0, v___x_5877_);
                    v___x_5880_ = v___x_5875_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5881_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5881_, 0, v___x_5877_);
                    lean_ctor_set(v_reuseFailAlloc_5881_, 1, v___x_5878_);
                    v___x_5880_ = v_reuseFailAlloc_5881_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Prod_map(
    mut v_00_u03b1_u2081_5883_: *mut LeanObject,
    mut v_00_u03b1_u2082_5884_: *mut LeanObject,
    mut v_00_u03b2_u2081_5885_: *mut LeanObject,
    mut v_00_u03b2_u2082_5886_: *mut LeanObject,
    mut v_f_5887_: *mut LeanObject,
    mut v_g_5888_: *mut LeanObject,
    mut v_x_5889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    v___x_5890_ = l_Prod_map___redArg(v_f_5887_, v_g_5888_, v_x_5889_);
    return v___x_5890_;
}
pub unsafe fn l_instDecidableEqSigma___redArg(
    mut v_h_u2081_5891_: *mut LeanObject,
    mut v_h_u2082_5892_: *mut LeanObject,
    mut v_x_5893_: *mut LeanObject,
    mut v_x_5894_: *mut LeanObject,
) -> u8 {
    let mut v_fst_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: u8 = 0;
    v_fst_5895_ = lean_ctor_get(v_x_5893_, 0);
    lean_inc_n(v_fst_5895_, 2);
    v_snd_5896_ = lean_ctor_get(v_x_5893_, 1);
    lean_inc(v_snd_5896_);
    lean_dec_ref(v_x_5893_);
    v_fst_5897_ = lean_ctor_get(v_x_5894_, 0);
    lean_inc(v_fst_5897_);
    v_snd_5898_ = lean_ctor_get(v_x_5894_, 1);
    lean_inc(v_snd_5898_);
    lean_dec_ref(v_x_5894_);
    v___x_5899_ = lean_apply_2(v_h_u2081_5891_, v_fst_5895_, v_fst_5897_);
    v___x_5900_ = (lean_unbox(v___x_5899_) as u8);
    if v___x_5900_ == 0 {
        let mut v___x_5901_: u8 = 0;
        lean_dec(v_snd_5898_);
        lean_dec(v_snd_5896_);
        lean_dec(v_fst_5895_);
        lean_dec_ref(v_h_u2082_5892_);
        v___x_5901_ = (lean_unbox(v___x_5899_) as u8);
        return v___x_5901_;
    } else {
        let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5903_: u8 = 0;
        v___x_5902_ = lean_apply_3(v_h_u2082_5892_, v_fst_5895_, v_snd_5896_, v_snd_5898_);
        v___x_5903_ = (lean_unbox(v___x_5902_) as u8);
        return v___x_5903_;
    }
}
pub unsafe fn l_instDecidableEqSigma___redArg___boxed(
    mut v_h_u2081_5904_: *mut LeanObject,
    mut v_h_u2082_5905_: *mut LeanObject,
    mut v_x_5906_: *mut LeanObject,
    mut v_x_5907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5908_: u8 = 0;
    let mut v_r_5909_: *mut LeanObject = core::ptr::null_mut();
    v_res_5908_ =
        l_instDecidableEqSigma___redArg(v_h_u2081_5904_, v_h_u2082_5905_, v_x_5906_, v_x_5907_);
    v_r_5909_ = lean_box((v_res_5908_) as usize);
    return v_r_5909_;
}
pub unsafe fn l_instDecidableEqSigma(
    mut v_00_u03b1_5910_: *mut LeanObject,
    mut v_00_u03b2_5911_: *mut LeanObject,
    mut v_h_u2081_5912_: *mut LeanObject,
    mut v_h_u2082_5913_: *mut LeanObject,
    mut v_x_5914_: *mut LeanObject,
    mut v_x_5915_: *mut LeanObject,
) -> u8 {
    let mut v___x_5916_: u8 = 0;
    v___x_5916_ =
        l_instDecidableEqSigma___redArg(v_h_u2081_5912_, v_h_u2082_5913_, v_x_5914_, v_x_5915_);
    return v___x_5916_;
}
pub unsafe fn l_instDecidableEqSigma___boxed(
    mut v_00_u03b1_5917_: *mut LeanObject,
    mut v_00_u03b2_5918_: *mut LeanObject,
    mut v_h_u2081_5919_: *mut LeanObject,
    mut v_h_u2082_5920_: *mut LeanObject,
    mut v_x_5921_: *mut LeanObject,
    mut v_x_5922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5923_: u8 = 0;
    let mut v_r_5924_: *mut LeanObject = core::ptr::null_mut();
    v_res_5923_ = l_instDecidableEqSigma(
        v_00_u03b1_5917_,
        v_00_u03b2_5918_,
        v_h_u2081_5919_,
        v_h_u2082_5920_,
        v_x_5921_,
        v_x_5922_,
    );
    v_r_5924_ = lean_box((v_res_5923_) as usize);
    return v_r_5924_;
}
pub unsafe fn l_instDecidableEqPSigma___redArg(
    mut v_h_u2081_5925_: *mut LeanObject,
    mut v_h_u2082_5926_: *mut LeanObject,
    mut v_x_5927_: *mut LeanObject,
    mut v_x_5928_: *mut LeanObject,
) -> u8 {
    let mut v_fst_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: u8 = 0;
    v_fst_5929_ = lean_ctor_get(v_x_5927_, 0);
    lean_inc_n(v_fst_5929_, 2);
    v_snd_5930_ = lean_ctor_get(v_x_5927_, 1);
    lean_inc(v_snd_5930_);
    lean_dec_ref(v_x_5927_);
    v_fst_5931_ = lean_ctor_get(v_x_5928_, 0);
    lean_inc(v_fst_5931_);
    v_snd_5932_ = lean_ctor_get(v_x_5928_, 1);
    lean_inc(v_snd_5932_);
    lean_dec_ref(v_x_5928_);
    v___x_5933_ = lean_apply_2(v_h_u2081_5925_, v_fst_5929_, v_fst_5931_);
    v___x_5934_ = (lean_unbox(v___x_5933_) as u8);
    if v___x_5934_ == 0 {
        let mut v___x_5935_: u8 = 0;
        lean_dec(v_snd_5932_);
        lean_dec(v_snd_5930_);
        lean_dec(v_fst_5929_);
        lean_dec_ref(v_h_u2082_5926_);
        v___x_5935_ = (lean_unbox(v___x_5933_) as u8);
        return v___x_5935_;
    } else {
        let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5937_: u8 = 0;
        v___x_5936_ = lean_apply_3(v_h_u2082_5926_, v_fst_5929_, v_snd_5930_, v_snd_5932_);
        v___x_5937_ = (lean_unbox(v___x_5936_) as u8);
        return v___x_5937_;
    }
}
pub unsafe fn l_instDecidableEqPSigma___redArg___boxed(
    mut v_h_u2081_5938_: *mut LeanObject,
    mut v_h_u2082_5939_: *mut LeanObject,
    mut v_x_5940_: *mut LeanObject,
    mut v_x_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5942_: u8 = 0;
    let mut v_r_5943_: *mut LeanObject = core::ptr::null_mut();
    v_res_5942_ =
        l_instDecidableEqPSigma___redArg(v_h_u2081_5938_, v_h_u2082_5939_, v_x_5940_, v_x_5941_);
    v_r_5943_ = lean_box((v_res_5942_) as usize);
    return v_r_5943_;
}
pub unsafe fn l_instDecidableEqPSigma(
    mut v_00_u03b1_5944_: *mut LeanObject,
    mut v_00_u03b2_5945_: *mut LeanObject,
    mut v_h_u2081_5946_: *mut LeanObject,
    mut v_h_u2082_5947_: *mut LeanObject,
    mut v_x_5948_: *mut LeanObject,
    mut v_x_5949_: *mut LeanObject,
) -> u8 {
    let mut v___x_5950_: u8 = 0;
    v___x_5950_ =
        l_instDecidableEqPSigma___redArg(v_h_u2081_5946_, v_h_u2082_5947_, v_x_5948_, v_x_5949_);
    return v___x_5950_;
}
pub unsafe fn l_instDecidableEqPSigma___boxed(
    mut v_00_u03b1_5951_: *mut LeanObject,
    mut v_00_u03b2_5952_: *mut LeanObject,
    mut v_h_u2081_5953_: *mut LeanObject,
    mut v_h_u2082_5954_: *mut LeanObject,
    mut v_x_5955_: *mut LeanObject,
    mut v_x_5956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5957_: u8 = 0;
    let mut v_r_5958_: *mut LeanObject = core::ptr::null_mut();
    v_res_5957_ = l_instDecidableEqPSigma(
        v_00_u03b1_5951_,
        v_00_u03b2_5952_,
        v_h_u2081_5953_,
        v_h_u2082_5954_,
        v_x_5955_,
        v_x_5956_,
    );
    v_r_5958_ = lean_box((v_res_5957_) as usize);
    return v_r_5958_;
}
pub unsafe fn _init_l_instInhabitedPUnit() -> *mut LeanObject {
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    v___x_5959_ = lean_box(0);
    return v___x_5959_;
}
pub unsafe fn l_instDecidableEqPUnit(
    mut v_a_5960_: *mut LeanObject,
    mut v_b_5961_: *mut LeanObject,
) -> u8 {
    let mut v___x_5962_: u8 = 0;
    v___x_5962_ = 1;
    return v___x_5962_;
}
pub unsafe fn l_instDecidableEqPUnit___boxed(
    mut v_a_5963_: *mut LeanObject,
    mut v_b_5964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5965_: u8 = 0;
    let mut v_r_5966_: *mut LeanObject = core::ptr::null_mut();
    v_res_5965_ = l_instDecidableEqPUnit(v_a_5963_, v_b_5964_);
    v_r_5966_ = lean_box((v_res_5965_) as usize);
    return v_r_5966_;
}
pub unsafe fn l_instHasEquivOfSetoid(
    mut v_00_u03b1_5967_: *mut LeanObject,
    mut v_inst_5968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    v___x_5969_ = lean_box(0);
    return v___x_5969_;
}
pub unsafe fn l_instDecidableEqOfIff___redArg(mut v_d_5970_: u8) -> u8 {
    return v_d_5970_;
}
pub unsafe fn l_instDecidableEqOfIff___redArg___boxed(
    mut v_d_5971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_boxed_5972_: u8 = 0;
    let mut v_res_5973_: u8 = 0;
    let mut v_r_5974_: *mut LeanObject = core::ptr::null_mut();
    v_d_boxed_5972_ = (lean_unbox(v_d_5971_) as u8);
    v_res_5973_ = l_instDecidableEqOfIff___redArg(v_d_boxed_5972_);
    v_r_5974_ = lean_box((v_res_5973_) as usize);
    return v_r_5974_;
}
pub unsafe fn l_instDecidableEqOfIff(
    mut v_p_5975_: *mut LeanObject,
    mut v_q_5976_: *mut LeanObject,
    mut v_d_5977_: u8,
) -> u8 {
    return v_d_5977_;
}
pub unsafe fn l_instDecidableEqOfIff___boxed(
    mut v_p_5978_: *mut LeanObject,
    mut v_q_5979_: *mut LeanObject,
    mut v_d_5980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_boxed_5981_: u8 = 0;
    let mut v_res_5982_: u8 = 0;
    let mut v_r_5983_: *mut LeanObject = core::ptr::null_mut();
    v_d_boxed_5981_ = (lean_unbox(v_d_5980_) as u8);
    v_res_5982_ = l_instDecidableEqOfIff(v_p_5978_, v_q_5979_, v_d_boxed_5981_);
    v_r_5983_ = lean_box((v_res_5982_) as usize);
    return v_r_5983_;
}
pub unsafe fn l_Not_elim(
    mut v_a_5984_: *mut LeanObject,
    mut v_00_u03b1_5985_: *mut LeanObject,
    mut v_H1_5986_: *mut LeanObject,
    mut v_H2_5987_: *mut LeanObject,
) -> *mut LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_And_elim___redArg(mut v_f_5988_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    v___x_5989_ = lean_apply_2(v_f_5988_, lean_box(0), lean_box(0));
    return v___x_5989_;
}
pub unsafe fn l_And_elim(
    mut v_a_5990_: *mut LeanObject,
    mut v_b_5991_: *mut LeanObject,
    mut v_00_u03b1_5992_: *mut LeanObject,
    mut v_f_5993_: *mut LeanObject,
    mut v_h_5994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    v___x_5995_ = lean_apply_2(v_f_5993_, lean_box(0), lean_box(0));
    return v___x_5995_;
}
pub unsafe fn l_Iff_elim___redArg(mut v_f_5996_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    v___x_5997_ = lean_apply_2(v_f_5996_, lean_box(0), lean_box(0));
    return v___x_5997_;
}
pub unsafe fn l_Iff_elim(
    mut v_a_5998_: *mut LeanObject,
    mut v_b_5999_: *mut LeanObject,
    mut v_00_u03b1_6000_: *mut LeanObject,
    mut v_f_6001_: *mut LeanObject,
    mut v_h_6002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    v___x_6003_ = lean_apply_2(v_f_6001_, lean_box(0), lean_box(0));
    return v___x_6003_;
}
pub unsafe fn l_Quot_liftOn___redArg(
    mut v_q_6004_: *mut LeanObject,
    mut v_f_6005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    v___x_6006_ = lean_apply_1(v_f_6005_, v_q_6004_);
    return v___x_6006_;
}
pub unsafe fn l_Quot_liftOn(
    mut v_00_u03b1_6007_: *mut LeanObject,
    mut v_00_u03b2_6008_: *mut LeanObject,
    mut v_r_6009_: *mut LeanObject,
    mut v_q_6010_: *mut LeanObject,
    mut v_f_6011_: *mut LeanObject,
    mut v_c_6012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    v___x_6013_ = lean_apply_1(v_f_6011_, v_q_6010_);
    return v___x_6013_;
}
pub unsafe fn l_Quot_rec___redArg(
    mut v_f_6014_: *mut LeanObject,
    mut v_q_6015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
    v___x_6016_ = lean_apply_1(v_f_6014_, v_q_6015_);
    return v___x_6016_;
}
pub unsafe fn l_Quot_rec(
    mut v_00_u03b1_6017_: *mut LeanObject,
    mut v_r_6018_: *mut LeanObject,
    mut v_motive_6019_: *mut LeanObject,
    mut v_f_6020_: *mut LeanObject,
    mut v_h_6021_: *mut LeanObject,
    mut v_q_6022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    v___x_6023_ = lean_apply_1(v_f_6020_, v_q_6022_);
    return v___x_6023_;
}
pub unsafe fn l_Quot_recOn___redArg(
    mut v_q_6024_: *mut LeanObject,
    mut v_f_6025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    v___x_6026_ = lean_apply_1(v_f_6025_, v_q_6024_);
    return v___x_6026_;
}
pub unsafe fn l_Quot_recOn(
    mut v_00_u03b1_6027_: *mut LeanObject,
    mut v_r_6028_: *mut LeanObject,
    mut v_motive_6029_: *mut LeanObject,
    mut v_q_6030_: *mut LeanObject,
    mut v_f_6031_: *mut LeanObject,
    mut v_h_6032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    v___x_6033_ = lean_apply_1(v_f_6031_, v_q_6030_);
    return v___x_6033_;
}
pub unsafe fn l_Quot_recOnSubsingleton___redArg(
    mut v_q_6034_: *mut LeanObject,
    mut v_f_6035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    v___x_6036_ = lean_apply_1(v_f_6035_, v_q_6034_);
    return v___x_6036_;
}
pub unsafe fn l_Quot_recOnSubsingleton(
    mut v_00_u03b1_6037_: *mut LeanObject,
    mut v_r_6038_: *mut LeanObject,
    mut v_motive_6039_: *mut LeanObject,
    mut v_h_6040_: *mut LeanObject,
    mut v_q_6041_: *mut LeanObject,
    mut v_f_6042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    v___x_6043_ = lean_apply_1(v_f_6042_, v_q_6041_);
    return v___x_6043_;
}
pub unsafe fn l_Quot_hrecOn___redArg(
    mut v_q_6044_: *mut LeanObject,
    mut v_f_6045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    v___x_6046_ = lean_apply_1(v_f_6045_, v_q_6044_);
    return v___x_6046_;
}
pub unsafe fn l_Quot_hrecOn(
    mut v_00_u03b1_6047_: *mut LeanObject,
    mut v_r_6048_: *mut LeanObject,
    mut v_motive_6049_: *mut LeanObject,
    mut v_q_6050_: *mut LeanObject,
    mut v_f_6051_: *mut LeanObject,
    mut v_c_6052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    v___x_6053_ = lean_apply_1(v_f_6051_, v_q_6050_);
    return v___x_6053_;
}
pub unsafe fn l_Quotient_mk___redArg(mut v_a_6054_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_6054_);
    return v_a_6054_;
}
pub unsafe fn l_Quotient_mk___redArg___boxed(mut v_a_6055_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6056_: *mut LeanObject = core::ptr::null_mut();
    v_res_6056_ = l_Quotient_mk___redArg(v_a_6055_);
    lean_dec(v_a_6055_);
    return v_res_6056_;
}
pub unsafe fn l_Quotient_mk(
    mut v_00_u03b1_6057_: *mut LeanObject,
    mut v_s_6058_: *mut LeanObject,
    mut v_a_6059_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_6059_);
    return v_a_6059_;
}
pub unsafe fn l_Quotient_mk___boxed(
    mut v_00_u03b1_6060_: *mut LeanObject,
    mut v_s_6061_: *mut LeanObject,
    mut v_a_6062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6063_: *mut LeanObject = core::ptr::null_mut();
    v_res_6063_ = l_Quotient_mk(v_00_u03b1_6060_, v_s_6061_, v_a_6062_);
    lean_dec(v_a_6062_);
    return v_res_6063_;
}
pub unsafe fn l_Quotient_mk_x27___redArg(mut v_a_6064_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_6064_);
    return v_a_6064_;
}
pub unsafe fn l_Quotient_mk_x27___redArg___boxed(
    mut v_a_6065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6066_: *mut LeanObject = core::ptr::null_mut();
    v_res_6066_ = l_Quotient_mk_x27___redArg(v_a_6065_);
    lean_dec(v_a_6065_);
    return v_res_6066_;
}
pub unsafe fn l_Quotient_mk_x27(
    mut v_00_u03b1_6067_: *mut LeanObject,
    mut v_s_6068_: *mut LeanObject,
    mut v_a_6069_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_6069_);
    return v_a_6069_;
}
pub unsafe fn l_Quotient_mk_x27___boxed(
    mut v_00_u03b1_6070_: *mut LeanObject,
    mut v_s_6071_: *mut LeanObject,
    mut v_a_6072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6073_: *mut LeanObject = core::ptr::null_mut();
    v_res_6073_ = l_Quotient_mk_x27(v_00_u03b1_6070_, v_s_6071_, v_a_6072_);
    lean_dec(v_a_6072_);
    return v_res_6073_;
}
pub unsafe fn l_Quotient_lift___redArg(
    mut v_f_6074_: *mut LeanObject,
    mut v_a_6075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    v___x_6076_ = lean_apply_1(v_f_6074_, v_a_6075_);
    return v___x_6076_;
}
pub unsafe fn l_Quotient_lift(
    mut v_00_u03b1_6077_: *mut LeanObject,
    mut v_00_u03b2_6078_: *mut LeanObject,
    mut v_s_6079_: *mut LeanObject,
    mut v_f_6080_: *mut LeanObject,
    mut v_a_6081_: *mut LeanObject,
    mut v_a_6082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    v___x_6083_ = lean_apply_1(v_f_6080_, v_a_6082_);
    return v___x_6083_;
}
pub unsafe fn l_Quotient_liftOn___redArg(
    mut v_q_6084_: *mut LeanObject,
    mut v_f_6085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    v___x_6086_ = lean_apply_1(v_f_6085_, v_q_6084_);
    return v___x_6086_;
}
pub unsafe fn l_Quotient_liftOn(
    mut v_00_u03b1_6087_: *mut LeanObject,
    mut v_00_u03b2_6088_: *mut LeanObject,
    mut v_s_6089_: *mut LeanObject,
    mut v_q_6090_: *mut LeanObject,
    mut v_f_6091_: *mut LeanObject,
    mut v_c_6092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    v___x_6093_ = lean_apply_1(v_f_6091_, v_q_6090_);
    return v___x_6093_;
}
pub unsafe fn l_Quotient_rec___redArg(
    mut v_f_6094_: *mut LeanObject,
    mut v_q_6095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    v___x_6096_ = lean_apply_1(v_f_6094_, v_q_6095_);
    return v___x_6096_;
}
pub unsafe fn l_Quotient_rec(
    mut v_00_u03b1_6097_: *mut LeanObject,
    mut v_s_6098_: *mut LeanObject,
    mut v_motive_6099_: *mut LeanObject,
    mut v_f_6100_: *mut LeanObject,
    mut v_h_6101_: *mut LeanObject,
    mut v_q_6102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6103_: *mut LeanObject = core::ptr::null_mut();
    v___x_6103_ = lean_apply_1(v_f_6100_, v_q_6102_);
    return v___x_6103_;
}
pub unsafe fn l_Quotient_recOn___redArg(
    mut v_q_6104_: *mut LeanObject,
    mut v_f_6105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    v___x_6106_ = lean_apply_1(v_f_6105_, v_q_6104_);
    return v___x_6106_;
}
pub unsafe fn l_Quotient_recOn(
    mut v_00_u03b1_6107_: *mut LeanObject,
    mut v_s_6108_: *mut LeanObject,
    mut v_motive_6109_: *mut LeanObject,
    mut v_q_6110_: *mut LeanObject,
    mut v_f_6111_: *mut LeanObject,
    mut v_h_6112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    v___x_6113_ = lean_apply_1(v_f_6111_, v_q_6110_);
    return v___x_6113_;
}
pub unsafe fn l_Quotient_recOnSubsingleton___redArg(
    mut v_q_6114_: *mut LeanObject,
    mut v_f_6115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    v___x_6116_ = lean_apply_1(v_f_6115_, v_q_6114_);
    return v___x_6116_;
}
pub unsafe fn l_Quotient_recOnSubsingleton(
    mut v_00_u03b1_6117_: *mut LeanObject,
    mut v_s_6118_: *mut LeanObject,
    mut v_motive_6119_: *mut LeanObject,
    mut v_h_6120_: *mut LeanObject,
    mut v_q_6121_: *mut LeanObject,
    mut v_f_6122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    v___x_6123_ = lean_apply_1(v_f_6122_, v_q_6121_);
    return v___x_6123_;
}
pub unsafe fn l_Quotient_hrecOn___redArg(
    mut v_q_6124_: *mut LeanObject,
    mut v_f_6125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    v___x_6126_ = lean_apply_1(v_f_6125_, v_q_6124_);
    return v___x_6126_;
}
pub unsafe fn l_Quotient_hrecOn(
    mut v_00_u03b1_6127_: *mut LeanObject,
    mut v_s_6128_: *mut LeanObject,
    mut v_motive_6129_: *mut LeanObject,
    mut v_q_6130_: *mut LeanObject,
    mut v_f_6131_: *mut LeanObject,
    mut v_c_6132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    v___x_6133_ = lean_apply_1(v_f_6131_, v_q_6130_);
    return v___x_6133_;
}
pub unsafe fn l_Quotient_lift_u2082___redArg(
    mut v_f_6134_: *mut LeanObject,
    mut v_q_u2081_6135_: *mut LeanObject,
    mut v_q_u2082_6136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    v___x_6137_ = lean_apply_2(v_f_6134_, v_q_u2081_6135_, v_q_u2082_6136_);
    return v___x_6137_;
}
pub unsafe fn l_Quotient_lift_u2082(
    mut v_00_u03b1_6138_: *mut LeanObject,
    mut v_00_u03b2_6139_: *mut LeanObject,
    mut v_00_u03c6_6140_: *mut LeanObject,
    mut v_s_u2081_6141_: *mut LeanObject,
    mut v_s_u2082_6142_: *mut LeanObject,
    mut v_f_6143_: *mut LeanObject,
    mut v_c_6144_: *mut LeanObject,
    mut v_q_u2081_6145_: *mut LeanObject,
    mut v_q_u2082_6146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    v___x_6147_ = lean_apply_2(v_f_6143_, v_q_u2081_6145_, v_q_u2082_6146_);
    return v___x_6147_;
}
pub unsafe fn l_Quotient_liftOn_u2082___redArg(
    mut v_q_u2081_6148_: *mut LeanObject,
    mut v_q_u2082_6149_: *mut LeanObject,
    mut v_f_6150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    v___x_6151_ = lean_apply_2(v_f_6150_, v_q_u2081_6148_, v_q_u2082_6149_);
    return v___x_6151_;
}
pub unsafe fn l_Quotient_liftOn_u2082(
    mut v_00_u03b1_6152_: *mut LeanObject,
    mut v_00_u03b2_6153_: *mut LeanObject,
    mut v_00_u03c6_6154_: *mut LeanObject,
    mut v_s_u2081_6155_: *mut LeanObject,
    mut v_s_u2082_6156_: *mut LeanObject,
    mut v_q_u2081_6157_: *mut LeanObject,
    mut v_q_u2082_6158_: *mut LeanObject,
    mut v_f_6159_: *mut LeanObject,
    mut v_c_6160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    v___x_6161_ = lean_apply_2(v_f_6159_, v_q_u2081_6157_, v_q_u2082_6158_);
    return v___x_6161_;
}
pub unsafe fn l_Quotient_recOnSubsingleton_u2082___redArg(
    mut v_q_u2081_6162_: *mut LeanObject,
    mut v_q_u2082_6163_: *mut LeanObject,
    mut v_g_6164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    v___x_6165_ = lean_apply_2(v_g_6164_, v_q_u2081_6162_, v_q_u2082_6163_);
    return v___x_6165_;
}
pub unsafe fn l_Quotient_recOnSubsingleton_u2082(
    mut v_00_u03b1_6166_: *mut LeanObject,
    mut v_00_u03b2_6167_: *mut LeanObject,
    mut v_s_u2081_6168_: *mut LeanObject,
    mut v_s_u2082_6169_: *mut LeanObject,
    mut v_motive_6170_: *mut LeanObject,
    mut v_s_6171_: *mut LeanObject,
    mut v_q_u2081_6172_: *mut LeanObject,
    mut v_q_u2082_6173_: *mut LeanObject,
    mut v_g_6174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    v___x_6175_ = lean_apply_2(v_g_6174_, v_q_u2081_6172_, v_q_u2082_6173_);
    return v___x_6175_;
}
pub unsafe fn l_Quotient_decidableEq___redArg(
    mut v_d_6176_: *mut LeanObject,
    mut v_q_u2081_6177_: *mut LeanObject,
    mut v_q_u2082_6178_: *mut LeanObject,
) -> u8 {
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: u8 = 0;
    v___x_6179_ = lean_apply_2(v_d_6176_, v_q_u2081_6177_, v_q_u2082_6178_);
    v___x_6180_ = (lean_unbox(v___x_6179_) as u8);
    return v___x_6180_;
}
pub unsafe fn l_Quotient_decidableEq___redArg___boxed(
    mut v_d_6181_: *mut LeanObject,
    mut v_q_u2081_6182_: *mut LeanObject,
    mut v_q_u2082_6183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6184_: u8 = 0;
    let mut v_r_6185_: *mut LeanObject = core::ptr::null_mut();
    v_res_6184_ = l_Quotient_decidableEq___redArg(v_d_6181_, v_q_u2081_6182_, v_q_u2082_6183_);
    v_r_6185_ = lean_box((v_res_6184_) as usize);
    return v_r_6185_;
}
pub unsafe fn l_Quotient_decidableEq(
    mut v_00_u03b1_6186_: *mut LeanObject,
    mut v_s_6187_: *mut LeanObject,
    mut v_d_6188_: *mut LeanObject,
    mut v_q_u2081_6189_: *mut LeanObject,
    mut v_q_u2082_6190_: *mut LeanObject,
) -> u8 {
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: u8 = 0;
    v___x_6191_ = lean_apply_2(v_d_6188_, v_q_u2081_6189_, v_q_u2082_6190_);
    v___x_6192_ = (lean_unbox(v___x_6191_) as u8);
    return v___x_6192_;
}
pub unsafe fn l_Quotient_decidableEq___boxed(
    mut v_00_u03b1_6193_: *mut LeanObject,
    mut v_s_6194_: *mut LeanObject,
    mut v_d_6195_: *mut LeanObject,
    mut v_q_u2081_6196_: *mut LeanObject,
    mut v_q_u2082_6197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6198_: u8 = 0;
    let mut v_r_6199_: *mut LeanObject = core::ptr::null_mut();
    v_res_6198_ = l_Quotient_decidableEq(
        v_00_u03b1_6193_,
        v_s_6194_,
        v_d_6195_,
        v_q_u2081_6196_,
        v_q_u2082_6197_,
    );
    v_r_6199_ = lean_box((v_res_6198_) as usize);
    return v_r_6199_;
}
pub unsafe fn l_Quot_pliftOn___redArg(
    mut v_q_6200_: *mut LeanObject,
    mut v_f_6201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
    v___x_6202_ = lean_apply_2(v_f_6201_, v_q_6200_, lean_box(0));
    return v___x_6202_;
}
pub unsafe fn l_Quot_pliftOn(
    mut v_00_u03b2_6203_: *mut LeanObject,
    mut v_00_u03b1_6204_: *mut LeanObject,
    mut v_r_6205_: *mut LeanObject,
    mut v_q_6206_: *mut LeanObject,
    mut v_f_6207_: *mut LeanObject,
    mut v_h_6208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6209_: *mut LeanObject = core::ptr::null_mut();
    v___x_6209_ = lean_apply_2(v_f_6207_, v_q_6206_, lean_box(0));
    return v___x_6209_;
}
pub unsafe fn l_Quotient_pliftOn___redArg(
    mut v_q_6210_: *mut LeanObject,
    mut v_f_6211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    v___x_6212_ = lean_apply_2(v_f_6211_, v_q_6210_, lean_box(0));
    return v___x_6212_;
}
pub unsafe fn l_Quotient_pliftOn(
    mut v_00_u03b2_6213_: *mut LeanObject,
    mut v_00_u03b1_6214_: *mut LeanObject,
    mut v_s_6215_: *mut LeanObject,
    mut v_q_6216_: *mut LeanObject,
    mut v_f_6217_: *mut LeanObject,
    mut v_h_6218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    v___x_6219_ = lean_apply_2(v_f_6217_, v_q_6216_, lean_box(0));
    return v___x_6219_;
}
pub unsafe fn l_Setoid_trivial(mut v_00_u03b1_6220_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    v___x_6221_ = lean_box(0);
    return v___x_6221_;
}
pub unsafe fn l_Squash_mk___redArg(mut v_x_6222_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_x_6222_);
    return v_x_6222_;
}
pub unsafe fn l_Squash_mk___redArg___boxed(mut v_x_6223_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6224_: *mut LeanObject = core::ptr::null_mut();
    v_res_6224_ = l_Squash_mk___redArg(v_x_6223_);
    lean_dec(v_x_6223_);
    return v_res_6224_;
}
pub unsafe fn l_Squash_mk(
    mut v_00_u03b1_6225_: *mut LeanObject,
    mut v_x_6226_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_6226_);
    return v_x_6226_;
}
pub unsafe fn l_Squash_mk___boxed(
    mut v_00_u03b1_6227_: *mut LeanObject,
    mut v_x_6228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6229_: *mut LeanObject = core::ptr::null_mut();
    v_res_6229_ = l_Squash_mk(v_00_u03b1_6227_, v_x_6228_);
    lean_dec(v_x_6228_);
    return v_res_6229_;
}
pub unsafe fn l_Squash_lift___redArg(
    mut v_s_6230_: *mut LeanObject,
    mut v_f_6231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    v___x_6232_ = lean_apply_1(v_f_6231_, v_s_6230_);
    return v___x_6232_;
}
pub unsafe fn l_Squash_lift(
    mut v_00_u03b1_6233_: *mut LeanObject,
    mut v_00_u03b2_6234_: *mut LeanObject,
    mut v_inst_6235_: *mut LeanObject,
    mut v_s_6236_: *mut LeanObject,
    mut v_f_6237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    v___x_6238_ = lean_apply_1(v_f_6237_, v_s_6236_);
    return v___x_6238_;
}
pub unsafe fn l_Lean_reduceBool(mut v_b_6239_: u8) -> u8 {
    return v_b_6239_;
}
pub unsafe fn l_Lean_reduceBool___boxed(mut v_b_6240_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_6241_: u8 = 0;
    let mut v_res_6242_: u8 = 0;
    let mut v_r_6243_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_6241_ = (lean_unbox(v_b_6240_) as u8);
    v_res_6242_ = l_Lean_reduceBool(v_b_boxed_6241_);
    v_r_6243_ = lean_box((v_res_6242_) as usize);
    return v_r_6243_;
}
pub unsafe fn l_Lean_reduceNat(mut v_n_6244_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_n_6244_);
    return v_n_6244_;
}
pub unsafe fn l_Lean_reduceNat___boxed(mut v_n_6245_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6246_: *mut LeanObject = core::ptr::null_mut();
    v_res_6246_ = l_Lean_reduceNat(v_n_6245_);
    lean_dec(v_n_6245_);
    return v_res_6246_;
}
pub unsafe fn l_Lean_opaqueId___redArg(mut v_x_6247_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_x_6247_);
    return v_x_6247_;
}
pub unsafe fn l_Lean_opaqueId___redArg___boxed(mut v_x_6248_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6249_: *mut LeanObject = core::ptr::null_mut();
    v_res_6249_ = l_Lean_opaqueId___redArg(v_x_6248_);
    lean_dec(v_x_6248_);
    return v_res_6249_;
}
pub unsafe fn l_Lean_opaqueId(
    mut v_00_u03b1_6250_: *mut LeanObject,
    mut v_x_6251_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_6251_);
    return v_x_6251_;
}
pub unsafe fn l_Lean_opaqueId___boxed(
    mut v_00_u03b1_6252_: *mut LeanObject,
    mut v_x_6253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6254_: *mut LeanObject = core::ptr::null_mut();
    v_res_6254_ = l_Lean_opaqueId(v_00_u03b1_6252_, v_x_6253_);
    lean_dec(v_x_6253_);
    return v_res_6254_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Core(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_SizeOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Task_Priority_default = _init_l_Task_Priority_default();
    lean_mark_persistent(l_Task_Priority_default);
    l_Task_Priority_max = _init_l_Task_Priority_max();
    lean_mark_persistent(l_Task_Priority_max);
    l_Task_Priority_dedicated = _init_l_Task_Priority_dedicated();
    lean_mark_persistent(l_Task_Priority_dedicated);
    l_instTransIff = _init_l_instTransIff();
    l_instDecidableTrue = _init_l_instDecidableTrue();
    l_instDecidableFalse = _init_l_instDecidableFalse();
    l_instInhabitedProp = _init_l_instInhabitedProp();
    l_instInhabitedNonScalar_default = _init_l_instInhabitedNonScalar_default();
    lean_mark_persistent(l_instInhabitedNonScalar_default);
    l_instInhabitedNonScalar = _init_l_instInhabitedNonScalar();
    lean_mark_persistent(l_instInhabitedNonScalar);
    l_instInhabitedPNonScalar_default = _init_l_instInhabitedPNonScalar_default();
    lean_mark_persistent(l_instInhabitedPNonScalar_default);
    l_instInhabitedPNonScalar = _init_l_instInhabitedPNonScalar();
    lean_mark_persistent(l_instInhabitedPNonScalar);
    l_instInhabitedTrue = _init_l_instInhabitedTrue();
    l_instInhabitedPUnit = _init_l_instInhabitedPUnit();
    lean_mark_persistent(l_instInhabitedPUnit);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Core(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Core(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_SizeOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Core(builtin);
}
