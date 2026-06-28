// Lean compiler output
// Module: Init.Control.Basic
// Imports: Init.Core Init.BinderNameHint
use crate::r#gen::Init::BinderNameHint::{
    initialize_Init_BinderNameHint, runtime_initialize_Init_BinderNameHint,
};
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unbox, lean_unsigned_to_nat,
};
pub static l_term___x3c_x26_x3e___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 101, 114, 109, 95, 60, 38, 62, 95, 0],
};
static mut l_term___x3c_x26_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__0_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__0_value) as *mut LeanObject,
        17902794450874024165 as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__1_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__2_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_term___x3c_x26_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__2_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__4_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 60, 38, 62, 32, 0],
};
static mut l_term___x3c_x26_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__4_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__4_value) as *mut LeanObject],
};
static mut l_term___x3c_x26_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__5_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__6_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_term___x3c_x26_x3e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__6_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__6_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x3e___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value) as *mut LeanObject,
        (((100 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x3e___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__8_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__8_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x3e___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__9_value) as *mut LeanObject;
pub static l_term___x3c_x26_x3e___00__closed__10_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__1_value) as *mut LeanObject,
        (((100 as usize) << 1) | 1) as *mut LeanObject,
        (((101 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__9_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x3e___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__10_value) as *mut LeanObject;
pub static mut l_term___x3c_x26_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__10_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value
) as *mut LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [70, 117, 110, 99, 116, 111, 114, 46, 109, 97, 112, 82, 101, 118, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5_value
) as *mut LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [70, 117, 110, 99, 116, 111, 114, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 97, 112, 82, 101, 118, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value
) as *mut LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value) as *mut LeanObject,2226500928782199335 as *mut LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value) as *mut LeanObject,17798854418672644188 as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1_value:
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
            l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value
        ) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1_value
) as *mut LeanObject;
pub static l_optional___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_optional___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_optional___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_optional___redArg___closed__0_value) as *mut LeanObject;
pub static l_instToBoolBool___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToBoolBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToBoolBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToBoolBool___closed__0_value) as *mut LeanObject;
pub static mut l_instToBoolBool: *mut LeanObject =
    core::ptr::addr_of!(l_instToBoolBool___closed__0_value) as *mut LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__0_value: LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 124, 124, 62, 95, 0],
    };
static mut l_term___x3c_x7c_x7c_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__0_value) as *mut LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__0_value) as *mut LeanObject,
        18177464721573610742 as *mut LeanObject,
    ],
};
static mut l_term___x3c_x7c_x7c_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__1_value) as *mut LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 60, 124, 124, 62, 32, 0],
};
static mut l_term___x3c_x7c_x7c_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__2_value) as *mut LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__2_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x7c_x7c_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__3_value) as *mut LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value) as *mut LeanObject,
        (((30 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x7c_x7c_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__4_value) as *mut LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x7c_x7c_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__5_value) as *mut LeanObject;
pub static l_term___x3c_x7c_x7c_x3e___00__closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__1_value) as *mut LeanObject,
        (((30 as usize) << 1) | 1) as *mut LeanObject,
        (((31 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__5_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x7c_x7c_x3e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__6_value) as *mut LeanObject;
pub static mut l_term___x3c_x7c_x7c_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x7c_x7c_x3e___00__closed__6_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 114, 77, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value) as *mut LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value) as *mut LeanObject,17806001628258047394 as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4_value) as *mut LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__0_value: LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 38, 38, 62, 95, 0],
    };
static mut l_term___x3c_x26_x26_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__0_value) as *mut LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__0_value) as *mut LeanObject,
        3935687535564439542 as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x26_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__1_value) as *mut LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 60, 38, 38, 62, 32, 0],
};
static mut l_term___x3c_x26_x26_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__2_value) as *mut LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__2_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x26_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__3_value) as *mut LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value) as *mut LeanObject,
        (((35 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x26_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__4_value) as *mut LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x26_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__5_value) as *mut LeanObject;
pub static l_term___x3c_x26_x26_x3e___00__closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__1_value) as *mut LeanObject,
        (((35 as usize) << 1) | 1) as *mut LeanObject,
        (((36 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__5_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x26_x26_x3e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__6_value) as *mut LeanObject;
pub static mut l_term___x3c_x26_x26_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x26_x26_x3e___00__closed__6_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 110, 100, 77, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value) as *mut LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value) as *mut LeanObject,8873471052530828183 as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4_value) as *mut LeanObject;
pub static l_instMonadControlTOfPure___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadControlTOfPure___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadControlTOfPure___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlTOfPure___redArg___closed__0_value) as *mut LeanObject;
pub static l_instMonadControlTOfPure___redArg___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadControlTOfPure___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_instMonadControlTOfPure___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_instMonadControlTOfPure___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlTOfPure___redArg___closed__1_value) as *mut LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 101, 114, 109, 95, 62, 61, 62, 95, 0],
};
static mut l_term___x3e_x3d_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__0_value) as *mut LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__0_value) as *mut LeanObject,
        376317980966388524 as *mut LeanObject,
    ],
};
static mut l_term___x3e_x3d_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__1_value) as *mut LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 62, 61, 62, 32, 0],
};
static mut l_term___x3e_x3d_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__2_value) as *mut LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___x3e_x3d_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__3_value) as *mut LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__7_value) as *mut LeanObject,
        (((55 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_term___x3e_x3d_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value) as *mut LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x3e_x3d_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__5_value) as *mut LeanObject;
pub static l_term___x3e_x3d_x3e___00__closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__1_value) as *mut LeanObject,
        (((55 as usize) << 1) | 1) as *mut LeanObject,
        (((56 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__5_value) as *mut LeanObject,
    ],
};
static mut l_term___x3e_x3d_x3e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__6_value) as *mut LeanObject;
pub static mut l_term___x3e_x3d_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__6_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [66, 105, 110, 100, 46, 107, 108, 101, 105, 115, 108, 105, 82, 105, 103, 104, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0_value
) as *mut LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 105, 110, 100, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [107, 108, 101, 105, 115, 108, 105, 82, 105, 103, 104, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value
) as *mut LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value) as *mut LeanObject,15820500991164727518 as *mut LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value) as *mut LeanObject,13518541916787333104 as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6_value
) as *mut LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 101, 114, 109, 95, 60, 61, 60, 95, 0],
};
static mut l_term___x3c_x3d_x3c___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__0_value) as *mut LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__0_value) as *mut LeanObject,
        6578201212627747956 as *mut LeanObject,
    ],
};
static mut l_term___x3c_x3d_x3c___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__1_value) as *mut LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 60, 61, 60, 32, 0],
};
static mut l_term___x3c_x3d_x3c___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__2_value) as *mut LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___x3c_x3d_x3c___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__3_value) as *mut LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x3d_x3c___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__4_value) as *mut LeanObject;
pub static l_term___x3c_x3d_x3c___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__1_value) as *mut LeanObject,
        (((55 as usize) << 1) | 1) as *mut LeanObject,
        (((56 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x3c_x3d_x3c___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___x3c_x3d_x3c__: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3c_x3d_x3c___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [66, 105, 110, 100, 46, 107, 108, 101, 105, 115, 108, 105, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0_value
) as *mut LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [107, 108, 101, 105, 115, 108, 105, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value
) as *mut LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value) as *mut LeanObject,15820500991164727518 as *mut LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value) as *mut LeanObject,2391163329140571260 as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5_value
) as *mut LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 101, 114, 109, 95, 61, 60, 60, 95, 0],
};
static mut l_term___x3d_x3c_x3c___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__0_value) as *mut LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__0_value) as *mut LeanObject,
        6202646376755925288 as *mut LeanObject,
    ],
};
static mut l_term___x3d_x3c_x3c___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__1_value) as *mut LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 61, 60, 60, 32, 0],
};
static mut l_term___x3d_x3c_x3c___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__2_value) as *mut LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__2_value) as *mut LeanObject],
};
static mut l_term___x3d_x3c_x3c___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__3_value) as *mut LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3c_x26_x3e___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3e_x3d_x3e___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x3d_x3c_x3c___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__4_value) as *mut LeanObject;
pub static l_term___x3d_x3c_x3c___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__1_value) as *mut LeanObject,
        (((55 as usize) << 1) | 1) as *mut LeanObject,
        (((56 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_term___x3d_x3c_x3c___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__5_value) as *mut LeanObject;
pub static mut l_term___x3d_x3c_x3c__: *mut LeanObject =
    core::ptr::addr_of!(l_term___x3d_x3c_x3c___00__closed__5_value) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [66, 105, 110, 100, 46, 98, 105, 110, 100, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0_value
) as *mut LeanObject;
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 105, 110, 100, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value
) as *mut LeanObject;
static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value) as *mut LeanObject,15820500991164727518 as *mut LeanObject] };
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value) as *mut LeanObject,10226104227652591212 as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value
) as *mut LeanObject;
pub static l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5_value
) as *mut LeanObject;
pub unsafe fn l_instForInOfForIn_x27___redArg___lam__0(
    mut v_f_860_: *mut LeanObject,
    mut v_a_861_: *mut LeanObject,
    mut v_x_862_: *mut LeanObject,
    mut v___y_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    v___x_864_ = lean_apply_2(v_f_860_, v_a_861_, v___y_863_);
    return v___x_864_;
}
pub unsafe fn l_instForInOfForIn_x27___redArg___lam__1(
    mut v_inst_865_: *mut LeanObject,
    mut v_00_u03b2_866_: *mut LeanObject,
    mut v_x_867_: *mut LeanObject,
    mut v_b_868_: *mut LeanObject,
    mut v_f_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    v___f_870_ = lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_870_, 0, v_f_869_);
    v___x_871_ = lean_apply_4(v_inst_865_, lean_box(0), v_x_867_, v_b_868_, v___f_870_);
    return v___x_871_;
}
pub unsafe fn l_instForInOfForIn_x27___redArg(mut v_inst_872_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_873_: *mut LeanObject = core::ptr::null_mut();
    v___f_873_ = lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_873_, 0, v_inst_872_);
    return v___f_873_;
}
pub unsafe fn l_instForInOfForIn_x27(
    mut v_m_874_: *mut LeanObject,
    mut v_00_u03c1_875_: *mut LeanObject,
    mut v_00_u03b1_876_: *mut LeanObject,
    mut v_d_877_: *mut LeanObject,
    mut v_inst_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_879_: *mut LeanObject = core::ptr::null_mut();
    v___f_879_ = lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_879_, 0, v_inst_878_);
    return v___f_879_;
}
pub unsafe fn l_ForInStep_value___redArg(mut v_x_880_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_881_: *mut LeanObject = core::ptr::null_mut();
    v_a_881_ = lean_ctor_get(v_x_880_, 0);
    lean_inc(v_a_881_);
    return v_a_881_;
}
pub unsafe fn l_ForInStep_value___redArg___boxed(mut v_x_882_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_883_: *mut LeanObject = core::ptr::null_mut();
    v_res_883_ = l_ForInStep_value___redArg(v_x_882_);
    lean_dec_ref(v_x_882_);
    return v_res_883_;
}
pub unsafe fn l_ForInStep_value(
    mut v_00_u03b1_884_: *mut LeanObject,
    mut v_x_885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_886_: *mut LeanObject = core::ptr::null_mut();
    v_a_886_ = lean_ctor_get(v_x_885_, 0);
    lean_inc(v_a_886_);
    return v_a_886_;
}
pub unsafe fn l_ForInStep_value___boxed(
    mut v_00_u03b1_887_: *mut LeanObject,
    mut v_x_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_889_: *mut LeanObject = core::ptr::null_mut();
    v_res_889_ = l_ForInStep_value(v_00_u03b1_887_, v_x_888_);
    lean_dec_ref(v_x_888_);
    return v_res_889_;
}
pub unsafe fn l_Functor_mapRev___redArg(
    mut v_inst_890_: *mut LeanObject,
    mut v_a_891_: *mut LeanObject,
    mut v_f_892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    v_map_893_ = lean_ctor_get(v_inst_890_, 0);
    lean_inc(v_map_893_);
    lean_dec_ref(v_inst_890_);
    v___x_894_ = lean_apply_4(v_map_893_, lean_box(0), lean_box(0), v_f_892_, v_a_891_);
    return v___x_894_;
}
pub unsafe fn l_Functor_mapRev(
    mut v_f_895_: *mut LeanObject,
    mut v_inst_896_: *mut LeanObject,
    mut v_00_u03b1_897_: *mut LeanObject,
    mut v_00_u03b2_898_: *mut LeanObject,
    mut v_a_899_: *mut LeanObject,
    mut v_f_900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    v___x_901_ = l_Functor_mapRev___redArg(v_inst_896_, v_a_899_, v_f_900_);
    return v___x_901_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6()
-> *mut LeanObject {
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    v___x_937_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5;
    v___x_938_ = l_String_toRawSubstring_x27(v___x_937_);
    return v___x_938_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1(
    mut v_x_953_: *mut LeanObject,
    mut v_a_954_: *mut LeanObject,
    mut v_a_955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u8 = 0;
    v___x_956_ = l_term___x3c_x26_x3e___00__closed__1;
    lean_inc(v_x_953_);
    v___x_957_ = l_Lean_Syntax_isOfKind(v_x_953_, v___x_956_);
    if v___x_957_ == 0 {
        let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_953_);
        v___x_958_ = lean_box(1);
        v___x_959_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_959_, 0, v___x_958_);
        lean_ctor_set(v___x_959_, 1, v_a_955_);
        return v___x_959_;
    } else {
        let mut v_quotContext_960_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_961_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_967_: u8 = 0;
        let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_960_ = lean_ctor_get(v_a_954_, 1);
        v_currMacroScope_961_ = lean_ctor_get(v_a_954_, 2);
        v_ref_962_ = lean_ctor_get(v_a_954_, 5);
        v___x_963_ = lean_unsigned_to_nat(0);
        v___x_964_ = l_Lean_Syntax_getArg(v_x_953_, v___x_963_);
        v___x_965_ = lean_unsigned_to_nat(2);
        v___x_966_ = l_Lean_Syntax_getArg(v_x_953_, v___x_965_);
        lean_dec(v_x_953_);
        v___x_967_ = 0;
        v___x_968_ = l_Lean_SourceInfo_fromRef(v_ref_962_, v___x_967_);
        v___x_969_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_970_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6);
        v___x_971_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9;
        lean_inc(v_currMacroScope_961_);
        lean_inc(v_quotContext_960_);
        v___x_972_ = l_Lean_addMacroScope(v_quotContext_960_, v___x_971_, v_currMacroScope_961_);
        v___x_973_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11;
        lean_inc_n(v___x_968_, 2);
        v___x_974_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_974_, 0, v___x_968_);
        lean_ctor_set(v___x_974_, 1, v___x_970_);
        lean_ctor_set(v___x_974_, 2, v___x_972_);
        lean_ctor_set(v___x_974_, 3, v___x_973_);
        v___x_975_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_976_ = l_Lean_Syntax_node2(v___x_968_, v___x_975_, v___x_964_, v___x_966_);
        v___x_977_ = l_Lean_Syntax_node2(v___x_968_, v___x_969_, v___x_974_, v___x_976_);
        v___x_978_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_978_, 0, v___x_977_);
        lean_ctor_set(v___x_978_, 1, v_a_955_);
        return v___x_978_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___boxed(
    mut v_x_979_: *mut LeanObject,
    mut v_a_980_: *mut LeanObject,
    mut v_a_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1(
        v_x_979_, v_a_980_, v_a_981_,
    );
    lean_dec_ref(v_a_980_);
    return v_res_982_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(
    mut v_x_986_: *mut LeanObject,
    mut v_a_987_: *mut LeanObject,
    mut v_a_988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    v___x_989_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    lean_inc(v_x_986_);
    v___x_990_ = l_Lean_Syntax_isOfKind(v_x_986_, v___x_989_);
    if v___x_990_ == 0 {
        let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_986_);
        v___x_991_ = lean_box(0);
        v___x_992_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_992_, 0, v___x_991_);
        lean_ctor_set(v___x_992_, 1, v_a_988_);
        return v___x_992_;
    } else {
        let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_996_: u8 = 0;
        v___x_993_ = lean_unsigned_to_nat(0);
        v___x_994_ = l_Lean_Syntax_getArg(v_x_986_, v___x_993_);
        v___x_995_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        lean_inc(v___x_994_);
        v___x_996_ = l_Lean_Syntax_isOfKind(v___x_994_, v___x_995_);
        if v___x_996_ == 0 {
            let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_994_);
            lean_dec(v_x_986_);
            v___x_997_ = lean_box(0);
            v___x_998_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_998_, 0, v___x_997_);
            lean_ctor_set(v___x_998_, 1, v_a_988_);
            return v___x_998_;
        } else {
            let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1002_: u8 = 0;
            v___x_999_ = lean_unsigned_to_nat(1);
            v___x_1000_ = l_Lean_Syntax_getArg(v_x_986_, v___x_999_);
            lean_dec(v_x_986_);
            v___x_1001_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1000_);
            v___x_1002_ = l_Lean_Syntax_matchesNull(v___x_1000_, v___x_1001_);
            if v___x_1002_ == 0 {
                let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1000_);
                lean_dec(v___x_994_);
                v___x_1003_ = lean_box(0);
                v___x_1004_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1004_, 0, v___x_1003_);
                lean_ctor_set(v___x_1004_, 1, v_a_988_);
                return v___x_1004_;
            } else {
                let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1007_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1008_: u8 = 0;
                let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
                v___x_1005_ = l_Lean_Syntax_getArg(v___x_1000_, v___x_993_);
                v___x_1006_ = l_Lean_Syntax_getArg(v___x_1000_, v___x_999_);
                lean_dec(v___x_1000_);
                v_ref_1007_ = l_Lean_replaceRef(v___x_994_, v_a_987_);
                lean_dec(v___x_994_);
                v___x_1008_ = 0;
                v___x_1009_ = l_Lean_SourceInfo_fromRef(v_ref_1007_, v___x_1008_);
                lean_dec(v_ref_1007_);
                v___x_1010_ = l_term___x3c_x26_x3e___00__closed__1;
                v___x_1011_ = l_term___x3c_x26_x3e___00__closed__4;
                lean_inc(v___x_1009_);
                v___x_1012_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1012_, 0, v___x_1009_);
                lean_ctor_set(v___x_1012_, 1, v___x_1011_);
                v___x_1013_ = l_Lean_Syntax_node3(
                    v___x_1009_,
                    v___x_1010_,
                    v___x_1005_,
                    v___x_1012_,
                    v___x_1006_,
                );
                v___x_1014_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1014_, 0, v___x_1013_);
                lean_ctor_set(v___x_1014_, 1, v_a_988_);
                return v___x_1014_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___boxed(
    mut v_x_1015_: *mut LeanObject,
    mut v_a_1016_: *mut LeanObject,
    mut v_a_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_res_1018_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(
        v_x_1015_, v_a_1016_, v_a_1017_,
    );
    lean_dec(v_a_1016_);
    return v_res_1018_;
}
pub unsafe fn l_Functor_discard___redArg(
    mut v_inst_1019_: *mut LeanObject,
    mut v_x_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mapConst_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    v_mapConst_1021_ = lean_ctor_get(v_inst_1019_, 1);
    lean_inc(v_mapConst_1021_);
    lean_dec_ref(v_inst_1019_);
    v___x_1022_ = lean_box(0);
    v___x_1023_ = lean_apply_4(
        v_mapConst_1021_,
        lean_box(0),
        lean_box(0),
        v___x_1022_,
        v_x_1020_,
    );
    return v___x_1023_;
}
pub unsafe fn l_Functor_discard(
    mut v_f_1024_: *mut LeanObject,
    mut v_00_u03b1_1025_: *mut LeanObject,
    mut v_inst_1026_: *mut LeanObject,
    mut v_x_1027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mapConst_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    v_mapConst_1028_ = lean_ctor_get(v_inst_1026_, 1);
    lean_inc(v_mapConst_1028_);
    lean_dec_ref(v_inst_1026_);
    v___x_1029_ = lean_box(0);
    v___x_1030_ = lean_apply_4(
        v_mapConst_1028_,
        lean_box(0),
        lean_box(0),
        v___x_1029_,
        v_x_1027_,
    );
    return v___x_1030_;
}
pub unsafe fn l_instOrElseOfAlternative___redArg(
    mut v_inst_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_1032_ = lean_ctor_get(v_inst_1031_, 2);
    lean_inc(v_orElse_1032_);
    lean_dec_ref(v_inst_1031_);
    v___x_1033_ = lean_apply_1(v_orElse_1032_, lean_box(0));
    return v___x_1033_;
}
pub unsafe fn l_instOrElseOfAlternative(
    mut v_f_1034_: *mut LeanObject,
    mut v_00_u03b1_1035_: *mut LeanObject,
    mut v_inst_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_instOrElseOfAlternative___redArg(v_inst_1036_);
    return v___x_1037_;
}
pub unsafe fn l_guard___redArg(
    mut v_inst_1038_: *mut LeanObject,
    mut v_inst_1039_: u8,
) -> *mut LeanObject {
    if v_inst_1039_ == 0 {
        let mut v_failure_1040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
        v_failure_1040_ = lean_ctor_get(v_inst_1038_, 1);
        lean_inc(v_failure_1040_);
        lean_dec_ref(v_inst_1038_);
        v___x_1041_ = lean_apply_1(v_failure_1040_, lean_box(0));
        return v___x_1041_;
    } else {
        let mut v_toApplicative_1042_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1043_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1042_ = lean_ctor_get(v_inst_1038_, 0);
        lean_inc_ref(v_toApplicative_1042_);
        lean_dec_ref(v_inst_1038_);
        v_toPure_1043_ = lean_ctor_get(v_toApplicative_1042_, 1);
        lean_inc(v_toPure_1043_);
        lean_dec_ref(v_toApplicative_1042_);
        v___x_1044_ = lean_box(0);
        v___x_1045_ = lean_apply_2(v_toPure_1043_, lean_box(0), v___x_1044_);
        return v___x_1045_;
    }
}
pub unsafe fn l_guard___redArg___boxed(
    mut v_inst_1046_: *mut LeanObject,
    mut v_inst_1047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_22__boxed_1048_: u8 = 0;
    let mut v_res_1049_: *mut LeanObject = core::ptr::null_mut();
    v_inst_22__boxed_1048_ = (lean_unbox(v_inst_1047_) as u8);
    v_res_1049_ = l_guard___redArg(v_inst_1046_, v_inst_22__boxed_1048_);
    return v_res_1049_;
}
pub unsafe fn l_guard(
    mut v_f_1050_: *mut LeanObject,
    mut v_inst_1051_: *mut LeanObject,
    mut v_p_1052_: *mut LeanObject,
    mut v_inst_1053_: u8,
) -> *mut LeanObject {
    if v_inst_1053_ == 0 {
        let mut v_failure_1054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
        v_failure_1054_ = lean_ctor_get(v_inst_1051_, 1);
        lean_inc(v_failure_1054_);
        lean_dec_ref(v_inst_1051_);
        v___x_1055_ = lean_apply_1(v_failure_1054_, lean_box(0));
        return v___x_1055_;
    } else {
        let mut v_toApplicative_1056_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_1056_ = lean_ctor_get(v_inst_1051_, 0);
        lean_inc_ref(v_toApplicative_1056_);
        lean_dec_ref(v_inst_1051_);
        v_toPure_1057_ = lean_ctor_get(v_toApplicative_1056_, 1);
        lean_inc(v_toPure_1057_);
        lean_dec_ref(v_toApplicative_1056_);
        v___x_1058_ = lean_box(0);
        v___x_1059_ = lean_apply_2(v_toPure_1057_, lean_box(0), v___x_1058_);
        return v___x_1059_;
    }
}
pub unsafe fn l_guard___boxed(
    mut v_f_1060_: *mut LeanObject,
    mut v_inst_1061_: *mut LeanObject,
    mut v_p_1062_: *mut LeanObject,
    mut v_inst_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_34__boxed_1064_: u8 = 0;
    let mut v_res_1065_: *mut LeanObject = core::ptr::null_mut();
    v_inst_34__boxed_1064_ = (lean_unbox(v_inst_1063_) as u8);
    v_res_1065_ = l_guard(v_f_1060_, v_inst_1061_, v_p_1062_, v_inst_34__boxed_1064_);
    return v_res_1065_;
}
pub unsafe fn l_optional___redArg___lam__0(mut v_val_1066_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___x_1067_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1067_, 0, v_val_1066_);
    return v___x_1067_;
}
pub unsafe fn l_optional___redArg___lam__1(
    mut v_toPure_1068_: *mut LeanObject,
    mut v_x_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    v___x_1070_ = lean_box(0);
    v___x_1071_ = lean_apply_2(v_toPure_1068_, lean_box(0), v___x_1070_);
    return v___x_1071_;
}
pub unsafe fn l_optional___redArg(
    mut v_inst_1073_: *mut LeanObject,
    mut v_x_1074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orElse_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1075_ = lean_ctor_get(v_inst_1073_, 0);
    lean_inc_ref(v_toApplicative_1075_);
    v_toFunctor_1076_ = lean_ctor_get(v_toApplicative_1075_, 0);
    lean_inc_ref(v_toFunctor_1076_);
    v_orElse_1077_ = lean_ctor_get(v_inst_1073_, 2);
    lean_inc(v_orElse_1077_);
    lean_dec_ref(v_inst_1073_);
    v_toPure_1078_ = lean_ctor_get(v_toApplicative_1075_, 1);
    lean_inc(v_toPure_1078_);
    lean_dec_ref(v_toApplicative_1075_);
    v_map_1079_ = lean_ctor_get(v_toFunctor_1076_, 0);
    lean_inc(v_map_1079_);
    lean_dec_ref(v_toFunctor_1076_);
    v___f_1080_ = l_optional___redArg___closed__0;
    v___f_1081_ = lean_alloc_closure(l_optional___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1081_, 0, v_toPure_1078_);
    v___x_1082_ = lean_apply_4(
        v_map_1079_,
        lean_box(0),
        lean_box(0),
        v___f_1080_,
        v_x_1074_,
    );
    v___x_1083_ = lean_apply_3(v_orElse_1077_, lean_box(0), v___x_1082_, v___f_1081_);
    return v___x_1083_;
}
pub unsafe fn l_optional(
    mut v_f_1084_: *mut LeanObject,
    mut v_inst_1085_: *mut LeanObject,
    mut v_00_u03b1_1086_: *mut LeanObject,
    mut v_x_1087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orElse_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1088_ = lean_ctor_get(v_inst_1085_, 0);
    lean_inc_ref(v_toApplicative_1088_);
    v_toFunctor_1089_ = lean_ctor_get(v_toApplicative_1088_, 0);
    lean_inc_ref(v_toFunctor_1089_);
    v_orElse_1090_ = lean_ctor_get(v_inst_1085_, 2);
    lean_inc(v_orElse_1090_);
    lean_dec_ref(v_inst_1085_);
    v_toPure_1091_ = lean_ctor_get(v_toApplicative_1088_, 1);
    lean_inc(v_toPure_1091_);
    lean_dec_ref(v_toApplicative_1088_);
    v_map_1092_ = lean_ctor_get(v_toFunctor_1089_, 0);
    lean_inc(v_map_1092_);
    lean_dec_ref(v_toFunctor_1089_);
    v___f_1093_ = l_optional___redArg___closed__0;
    v___f_1094_ = lean_alloc_closure(l_optional___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1094_, 0, v_toPure_1091_);
    v___x_1095_ = lean_apply_4(
        v_map_1092_,
        lean_box(0),
        lean_box(0),
        v___f_1093_,
        v_x_1087_,
    );
    v___x_1096_ = lean_apply_3(v_orElse_1090_, lean_box(0), v___x_1095_, v___f_1094_);
    return v___x_1096_;
}
pub unsafe fn l_instToBoolBool___lam__0(mut v_b_1097_: u8) -> u8 {
    return v_b_1097_;
}
pub unsafe fn l_instToBoolBool___lam__0___boxed(mut v_b_1098_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_1099_: u8 = 0;
    let mut v_res_1100_: u8 = 0;
    let mut v_r_1101_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_1099_ = (lean_unbox(v_b_1098_) as u8);
    v_res_1100_ = l_instToBoolBool___lam__0(v_b_boxed_1099_);
    v_r_1101_ = lean_box((v_res_1100_) as usize);
    return v_r_1101_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1()
-> *mut LeanObject {
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    v___x_1124_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0;
    v___x_1125_ = l_String_toRawSubstring_x27(v___x_1124_);
    return v___x_1125_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(
    mut v_x_1134_: *mut LeanObject,
    mut v_a_1135_: *mut LeanObject,
    mut v_a_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: u8 = 0;
    v___x_1137_ = l_term___x3c_x7c_x7c_x3e___00__closed__1;
    lean_inc(v_x_1134_);
    v___x_1138_ = l_Lean_Syntax_isOfKind(v_x_1134_, v___x_1137_);
    if v___x_1138_ == 0 {
        let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1134_);
        v___x_1139_ = lean_box(1);
        v___x_1140_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1140_, 0, v___x_1139_);
        lean_ctor_set(v___x_1140_, 1, v_a_1136_);
        return v___x_1140_;
    } else {
        let mut v_quotContext_1141_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1142_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1148_: u8 = 0;
        let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1141_ = lean_ctor_get(v_a_1135_, 1);
        v_currMacroScope_1142_ = lean_ctor_get(v_a_1135_, 2);
        v_ref_1143_ = lean_ctor_get(v_a_1135_, 5);
        v___x_1144_ = lean_unsigned_to_nat(0);
        v___x_1145_ = l_Lean_Syntax_getArg(v_x_1134_, v___x_1144_);
        v___x_1146_ = lean_unsigned_to_nat(2);
        v___x_1147_ = l_Lean_Syntax_getArg(v_x_1134_, v___x_1146_);
        lean_dec(v_x_1134_);
        v___x_1148_ = 0;
        v___x_1149_ = l_Lean_SourceInfo_fromRef(v_ref_1143_, v___x_1148_);
        v___x_1150_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1151_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1);
        v___x_1152_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2;
        lean_inc(v_currMacroScope_1142_);
        lean_inc(v_quotContext_1141_);
        v___x_1153_ =
            l_Lean_addMacroScope(v_quotContext_1141_, v___x_1152_, v_currMacroScope_1142_);
        v___x_1154_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4;
        lean_inc_n(v___x_1149_, 2);
        v___x_1155_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1155_, 0, v___x_1149_);
        lean_ctor_set(v___x_1155_, 1, v___x_1151_);
        lean_ctor_set(v___x_1155_, 2, v___x_1153_);
        lean_ctor_set(v___x_1155_, 3, v___x_1154_);
        v___x_1156_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1157_ = l_Lean_Syntax_node2(v___x_1149_, v___x_1156_, v___x_1145_, v___x_1147_);
        v___x_1158_ = l_Lean_Syntax_node2(v___x_1149_, v___x_1150_, v___x_1155_, v___x_1157_);
        v___x_1159_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1159_, 0, v___x_1158_);
        lean_ctor_set(v___x_1159_, 1, v_a_1136_);
        return v___x_1159_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___boxed(
    mut v_x_1160_: *mut LeanObject,
    mut v_a_1161_: *mut LeanObject,
    mut v_a_1162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1163_: *mut LeanObject = core::ptr::null_mut();
    v_res_1163_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(
        v_x_1160_, v_a_1161_, v_a_1162_,
    );
    lean_dec_ref(v_a_1161_);
    return v_res_1163_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__orM__1(
    mut v_x_1164_: *mut LeanObject,
    mut v_a_1165_: *mut LeanObject,
    mut v_a_1166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u8 = 0;
    v___x_1167_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    lean_inc(v_x_1164_);
    v___x_1168_ = l_Lean_Syntax_isOfKind(v_x_1164_, v___x_1167_);
    if v___x_1168_ == 0 {
        let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1164_);
        v___x_1169_ = lean_box(0);
        v___x_1170_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1170_, 0, v___x_1169_);
        lean_ctor_set(v___x_1170_, 1, v_a_1166_);
        return v___x_1170_;
    } else {
        let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: u8 = 0;
        v___x_1171_ = lean_unsigned_to_nat(0);
        v___x_1172_ = l_Lean_Syntax_getArg(v_x_1164_, v___x_1171_);
        v___x_1173_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        lean_inc(v___x_1172_);
        v___x_1174_ = l_Lean_Syntax_isOfKind(v___x_1172_, v___x_1173_);
        if v___x_1174_ == 0 {
            let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1172_);
            lean_dec(v_x_1164_);
            v___x_1175_ = lean_box(0);
            v___x_1176_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1176_, 0, v___x_1175_);
            lean_ctor_set(v___x_1176_, 1, v_a_1166_);
            return v___x_1176_;
        } else {
            let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1180_: u8 = 0;
            v___x_1177_ = lean_unsigned_to_nat(1);
            v___x_1178_ = l_Lean_Syntax_getArg(v_x_1164_, v___x_1177_);
            lean_dec(v_x_1164_);
            v___x_1179_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1178_);
            v___x_1180_ = l_Lean_Syntax_matchesNull(v___x_1178_, v___x_1179_);
            if v___x_1180_ == 0 {
                let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1178_);
                lean_dec(v___x_1172_);
                v___x_1181_ = lean_box(0);
                v___x_1182_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1182_, 0, v___x_1181_);
                lean_ctor_set(v___x_1182_, 1, v_a_1166_);
                return v___x_1182_;
            } else {
                let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1185_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1186_: u8 = 0;
                let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
                v___x_1183_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_1171_);
                v___x_1184_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_1177_);
                lean_dec(v___x_1178_);
                v_ref_1185_ = l_Lean_replaceRef(v___x_1172_, v_a_1165_);
                lean_dec(v___x_1172_);
                v___x_1186_ = 0;
                v___x_1187_ = l_Lean_SourceInfo_fromRef(v_ref_1185_, v___x_1186_);
                lean_dec(v_ref_1185_);
                v___x_1188_ = l_term___x3c_x7c_x7c_x3e___00__closed__1;
                v___x_1189_ = l_term___x3c_x7c_x7c_x3e___00__closed__2;
                lean_inc(v___x_1187_);
                v___x_1190_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1190_, 0, v___x_1187_);
                lean_ctor_set(v___x_1190_, 1, v___x_1189_);
                v___x_1191_ = l_Lean_Syntax_node3(
                    v___x_1187_,
                    v___x_1188_,
                    v___x_1183_,
                    v___x_1190_,
                    v___x_1184_,
                );
                v___x_1192_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1192_, 0, v___x_1191_);
                lean_ctor_set(v___x_1192_, 1, v_a_1166_);
                return v___x_1192_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__orM__1___boxed(
    mut v_x_1193_: *mut LeanObject,
    mut v_a_1194_: *mut LeanObject,
    mut v_a_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1196_: *mut LeanObject = core::ptr::null_mut();
    v_res_1196_ =
        l___aux__Init__Control__Basic______unexpand__orM__1(v_x_1193_, v_a_1194_, v_a_1195_);
    lean_dec(v_a_1194_);
    return v_res_1196_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1()
-> *mut LeanObject {
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    v___x_1217_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0;
    v___x_1218_ = l_String_toRawSubstring_x27(v___x_1217_);
    return v___x_1218_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(
    mut v_x_1227_: *mut LeanObject,
    mut v_a_1228_: *mut LeanObject,
    mut v_a_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: u8 = 0;
    v___x_1230_ = l_term___x3c_x26_x26_x3e___00__closed__1;
    lean_inc(v_x_1227_);
    v___x_1231_ = l_Lean_Syntax_isOfKind(v_x_1227_, v___x_1230_);
    if v___x_1231_ == 0 {
        let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1227_);
        v___x_1232_ = lean_box(1);
        v___x_1233_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1233_, 0, v___x_1232_);
        lean_ctor_set(v___x_1233_, 1, v_a_1229_);
        return v___x_1233_;
    } else {
        let mut v_quotContext_1234_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1235_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: u8 = 0;
        let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1234_ = lean_ctor_get(v_a_1228_, 1);
        v_currMacroScope_1235_ = lean_ctor_get(v_a_1228_, 2);
        v_ref_1236_ = lean_ctor_get(v_a_1228_, 5);
        v___x_1237_ = lean_unsigned_to_nat(0);
        v___x_1238_ = l_Lean_Syntax_getArg(v_x_1227_, v___x_1237_);
        v___x_1239_ = lean_unsigned_to_nat(2);
        v___x_1240_ = l_Lean_Syntax_getArg(v_x_1227_, v___x_1239_);
        lean_dec(v_x_1227_);
        v___x_1241_ = 0;
        v___x_1242_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1241_);
        v___x_1243_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1244_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1);
        v___x_1245_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2;
        lean_inc(v_currMacroScope_1235_);
        lean_inc(v_quotContext_1234_);
        v___x_1246_ =
            l_Lean_addMacroScope(v_quotContext_1234_, v___x_1245_, v_currMacroScope_1235_);
        v___x_1247_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4;
        lean_inc_n(v___x_1242_, 2);
        v___x_1248_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1248_, 0, v___x_1242_);
        lean_ctor_set(v___x_1248_, 1, v___x_1244_);
        lean_ctor_set(v___x_1248_, 2, v___x_1246_);
        lean_ctor_set(v___x_1248_, 3, v___x_1247_);
        v___x_1249_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1250_ = l_Lean_Syntax_node2(v___x_1242_, v___x_1249_, v___x_1238_, v___x_1240_);
        v___x_1251_ = l_Lean_Syntax_node2(v___x_1242_, v___x_1243_, v___x_1248_, v___x_1250_);
        v___x_1252_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1252_, 0, v___x_1251_);
        lean_ctor_set(v___x_1252_, 1, v_a_1229_);
        return v___x_1252_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___boxed(
    mut v_x_1253_: *mut LeanObject,
    mut v_a_1254_: *mut LeanObject,
    mut v_a_1255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1256_: *mut LeanObject = core::ptr::null_mut();
    v_res_1256_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(
        v_x_1253_, v_a_1254_, v_a_1255_,
    );
    lean_dec_ref(v_a_1254_);
    return v_res_1256_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__andM__1(
    mut v_x_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: u8 = 0;
    v___x_1260_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    lean_inc(v_x_1257_);
    v___x_1261_ = l_Lean_Syntax_isOfKind(v_x_1257_, v___x_1260_);
    if v___x_1261_ == 0 {
        let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1257_);
        v___x_1262_ = lean_box(0);
        v___x_1263_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1263_, 0, v___x_1262_);
        lean_ctor_set(v___x_1263_, 1, v_a_1259_);
        return v___x_1263_;
    } else {
        let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: u8 = 0;
        v___x_1264_ = lean_unsigned_to_nat(0);
        v___x_1265_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1264_);
        v___x_1266_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        lean_inc(v___x_1265_);
        v___x_1267_ = l_Lean_Syntax_isOfKind(v___x_1265_, v___x_1266_);
        if v___x_1267_ == 0 {
            let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1265_);
            lean_dec(v_x_1257_);
            v___x_1268_ = lean_box(0);
            v___x_1269_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1269_, 0, v___x_1268_);
            lean_ctor_set(v___x_1269_, 1, v_a_1259_);
            return v___x_1269_;
        } else {
            let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1273_: u8 = 0;
            v___x_1270_ = lean_unsigned_to_nat(1);
            v___x_1271_ = l_Lean_Syntax_getArg(v_x_1257_, v___x_1270_);
            lean_dec(v_x_1257_);
            v___x_1272_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1271_);
            v___x_1273_ = l_Lean_Syntax_matchesNull(v___x_1271_, v___x_1272_);
            if v___x_1273_ == 0 {
                let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1271_);
                lean_dec(v___x_1265_);
                v___x_1274_ = lean_box(0);
                v___x_1275_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1275_, 0, v___x_1274_);
                lean_ctor_set(v___x_1275_, 1, v_a_1259_);
                return v___x_1275_;
            } else {
                let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1278_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1279_: u8 = 0;
                let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
                v___x_1276_ = l_Lean_Syntax_getArg(v___x_1271_, v___x_1264_);
                v___x_1277_ = l_Lean_Syntax_getArg(v___x_1271_, v___x_1270_);
                lean_dec(v___x_1271_);
                v_ref_1278_ = l_Lean_replaceRef(v___x_1265_, v_a_1258_);
                lean_dec(v___x_1265_);
                v___x_1279_ = 0;
                v___x_1280_ = l_Lean_SourceInfo_fromRef(v_ref_1278_, v___x_1279_);
                lean_dec(v_ref_1278_);
                v___x_1281_ = l_term___x3c_x26_x26_x3e___00__closed__1;
                v___x_1282_ = l_term___x3c_x26_x26_x3e___00__closed__2;
                lean_inc(v___x_1280_);
                v___x_1283_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1283_, 0, v___x_1280_);
                lean_ctor_set(v___x_1283_, 1, v___x_1282_);
                v___x_1284_ = l_Lean_Syntax_node3(
                    v___x_1280_,
                    v___x_1281_,
                    v___x_1276_,
                    v___x_1283_,
                    v___x_1277_,
                );
                v___x_1285_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1285_, 0, v___x_1284_);
                lean_ctor_set(v___x_1285_, 1, v_a_1259_);
                return v___x_1285_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__andM__1___boxed(
    mut v_x_1286_: *mut LeanObject,
    mut v_a_1287_: *mut LeanObject,
    mut v_a_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1289_: *mut LeanObject = core::ptr::null_mut();
    v_res_1289_ =
        l___aux__Init__Control__Basic______unexpand__andM__1(v_x_1286_, v_a_1287_, v_a_1288_);
    lean_dec(v_a_1287_);
    return v_res_1289_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__0(
    mut v_x_u2082_1290_: *mut LeanObject,
    mut v_x_u2081_1291_: *mut LeanObject,
    mut v_00_u03b2_1292_: *mut LeanObject,
    mut v___y_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    v___x_1294_ = lean_apply_2(v_x_u2082_1290_, lean_box(0), v___y_1293_);
    v___x_1295_ = lean_apply_2(v_x_u2081_1291_, lean_box(0), v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__1(
    mut v_x_u2082_1296_: *mut LeanObject,
    mut v_f_1297_: *mut LeanObject,
    mut v_x_u2081_1298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    v___f_1299_ = lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1299_, 0, v_x_u2082_1296_);
    lean_closure_set(v___f_1299_, 1, v_x_u2081_1298_);
    v___x_1300_ = lean_apply_1(v_f_1297_, v___f_1299_);
    return v___x_1300_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__2(
    mut v_inst_1301_: *mut LeanObject,
    mut v_f_1302_: *mut LeanObject,
    mut v_x_u2082_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_liftWith_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    v_liftWith_1304_ = lean_ctor_get(v_inst_1301_, 0);
    lean_inc(v_liftWith_1304_);
    lean_dec_ref(v_inst_1301_);
    v___f_1305_ = lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1305_, 0, v_x_u2082_1303_);
    lean_closure_set(v___f_1305_, 1, v_f_1302_);
    v___x_1306_ = lean_apply_2(v_liftWith_1304_, lean_box(0), v___f_1305_);
    return v___x_1306_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__3(
    mut v_inst_1307_: *mut LeanObject,
    mut v_inst_1308_: *mut LeanObject,
    mut v_00_u03b1_1309_: *mut LeanObject,
    mut v_f_1310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_liftWith_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    v_liftWith_1311_ = lean_ctor_get(v_inst_1307_, 0);
    lean_inc(v_liftWith_1311_);
    lean_dec_ref(v_inst_1307_);
    v___f_1312_ = lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1312_, 0, v_inst_1308_);
    lean_closure_set(v___f_1312_, 1, v_f_1310_);
    v___x_1313_ = lean_apply_2(v_liftWith_1311_, lean_box(0), v___f_1312_);
    return v___x_1313_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg___lam__4(
    mut v_inst_1314_: *mut LeanObject,
    mut v_inst_1315_: *mut LeanObject,
    mut v_00_u03b1_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_restoreM_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    v_restoreM_1318_ = lean_ctor_get(v_inst_1314_, 1);
    lean_inc(v_restoreM_1318_);
    lean_dec_ref(v_inst_1314_);
    v_restoreM_1319_ = lean_ctor_get(v_inst_1315_, 1);
    lean_inc(v_restoreM_1319_);
    lean_dec_ref(v_inst_1315_);
    v___x_1320_ = lean_apply_2(v_restoreM_1319_, lean_box(0), v___y_1317_);
    v___x_1321_ = lean_apply_2(v_restoreM_1318_, lean_box(0), v___x_1320_);
    return v___x_1321_;
}
pub unsafe fn l_instMonadControlTOfMonadControl___redArg(
    mut v_inst_1322_: *mut LeanObject,
    mut v_inst_1323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1323_);
    lean_inc_ref(v_inst_1322_);
    v___f_1324_ = lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1324_, 0, v_inst_1322_);
    lean_closure_set(v___f_1324_, 1, v_inst_1323_);
    v___f_1325_ = lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1325_, 0, v_inst_1322_);
    lean_closure_set(v___f_1325_, 1, v_inst_1323_);
    v___x_1326_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1326_, 0, v___f_1324_);
    lean_ctor_set(v___x_1326_, 1, v___f_1325_);
    return v___x_1326_;
}
pub unsafe fn l_instMonadControlTOfMonadControl(
    mut v_m_1327_: *mut LeanObject,
    mut v_n_1328_: *mut LeanObject,
    mut v_o_1329_: *mut LeanObject,
    mut v_inst_1330_: *mut LeanObject,
    mut v_inst_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1331_);
    lean_inc_ref(v_inst_1330_);
    v___f_1332_ = lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__3 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1332_, 0, v_inst_1330_);
    lean_closure_set(v___f_1332_, 1, v_inst_1331_);
    v___f_1333_ = lean_alloc_closure(
        l_instMonadControlTOfMonadControl___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1333_, 0, v_inst_1330_);
    lean_closure_set(v___f_1333_, 1, v_inst_1331_);
    v___x_1334_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1334_, 0, v___f_1332_);
    lean_ctor_set(v___x_1334_, 1, v___f_1333_);
    return v___x_1334_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__0(
    mut v_00_u03b2_1335_: *mut LeanObject,
    mut v_x_1336_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1336_);
    return v_x_1336_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__0___boxed(
    mut v_00_u03b2_1337_: *mut LeanObject,
    mut v_x_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1339_: *mut LeanObject = core::ptr::null_mut();
    v_res_1339_ = l_instMonadControlTOfPure___redArg___lam__0(v_00_u03b2_1337_, v_x_1338_);
    lean_dec(v_x_1338_);
    return v_res_1339_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__1(
    mut v___f_1340_: *mut LeanObject,
    mut v_00_u03b1_1341_: *mut LeanObject,
    mut v_f_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    v___x_1343_ = lean_apply_1(v_f_1342_, v___f_1340_);
    return v___x_1343_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg___lam__2(
    mut v_inst_1344_: *mut LeanObject,
    mut v_00_u03b1_1345_: *mut LeanObject,
    mut v_x_1346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = lean_apply_2(v_inst_1344_, lean_box(0), v_x_1346_);
    return v___x_1347_;
}
pub unsafe fn l_instMonadControlTOfPure___redArg(
    mut v_inst_1351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    v___f_1352_ = l_instMonadControlTOfPure___redArg___closed__1;
    v___f_1353_ = lean_alloc_closure(
        l_instMonadControlTOfPure___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1353_, 0, v_inst_1351_);
    v___x_1354_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1354_, 0, v___f_1352_);
    lean_ctor_set(v___x_1354_, 1, v___f_1353_);
    return v___x_1354_;
}
pub unsafe fn l_instMonadControlTOfPure(
    mut v_m_1355_: *mut LeanObject,
    mut v_inst_1356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_instMonadControlTOfPure___redArg(v_inst_1356_);
    return v___x_1357_;
}
pub unsafe fn l_controlAt___redArg(
    mut v_inst_1358_: *mut LeanObject,
    mut v_inst_1359_: *mut LeanObject,
    mut v_f_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_liftWith_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    v_liftWith_1361_ = lean_ctor_get(v_inst_1358_, 0);
    lean_inc(v_liftWith_1361_);
    v_restoreM_1362_ = lean_ctor_get(v_inst_1358_, 1);
    lean_inc(v_restoreM_1362_);
    lean_dec_ref(v_inst_1358_);
    v___x_1363_ = lean_apply_2(v_liftWith_1361_, lean_box(0), v_f_1360_);
    v___x_1364_ = lean_apply_1(v_restoreM_1362_, lean_box(0));
    v___x_1365_ = lean_apply_4(
        v_inst_1359_,
        lean_box(0),
        lean_box(0),
        v___x_1363_,
        v___x_1364_,
    );
    return v___x_1365_;
}
pub unsafe fn l_controlAt(
    mut v_m_1366_: *mut LeanObject,
    mut v_n_1367_: *mut LeanObject,
    mut v_inst_1368_: *mut LeanObject,
    mut v_inst_1369_: *mut LeanObject,
    mut v_00_u03b1_1370_: *mut LeanObject,
    mut v_f_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_liftWith_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v_liftWith_1372_ = lean_ctor_get(v_inst_1368_, 0);
    lean_inc(v_liftWith_1372_);
    v_restoreM_1373_ = lean_ctor_get(v_inst_1368_, 1);
    lean_inc(v_restoreM_1373_);
    lean_dec_ref(v_inst_1368_);
    v___x_1374_ = lean_apply_2(v_liftWith_1372_, lean_box(0), v_f_1371_);
    v___x_1375_ = lean_apply_1(v_restoreM_1373_, lean_box(0));
    v___x_1376_ = lean_apply_4(
        v_inst_1369_,
        lean_box(0),
        lean_box(0),
        v___x_1374_,
        v___x_1375_,
    );
    return v___x_1376_;
}
pub unsafe fn l_control___redArg(
    mut v_inst_1377_: *mut LeanObject,
    mut v_inst_1378_: *mut LeanObject,
    mut v_f_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_liftWith_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    v_liftWith_1380_ = lean_ctor_get(v_inst_1377_, 0);
    lean_inc(v_liftWith_1380_);
    v_restoreM_1381_ = lean_ctor_get(v_inst_1377_, 1);
    lean_inc(v_restoreM_1381_);
    lean_dec_ref(v_inst_1377_);
    v___x_1382_ = lean_apply_2(v_liftWith_1380_, lean_box(0), v_f_1379_);
    v___x_1383_ = lean_apply_1(v_restoreM_1381_, lean_box(0));
    v___x_1384_ = lean_apply_4(
        v_inst_1378_,
        lean_box(0),
        lean_box(0),
        v___x_1382_,
        v___x_1383_,
    );
    return v___x_1384_;
}
pub unsafe fn l_control(
    mut v_m_1385_: *mut LeanObject,
    mut v_n_1386_: *mut LeanObject,
    mut v_inst_1387_: *mut LeanObject,
    mut v_inst_1388_: *mut LeanObject,
    mut v_00_u03b1_1389_: *mut LeanObject,
    mut v_f_1390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_liftWith_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    v_liftWith_1391_ = lean_ctor_get(v_inst_1387_, 0);
    lean_inc(v_liftWith_1391_);
    v_restoreM_1392_ = lean_ctor_get(v_inst_1387_, 1);
    lean_inc(v_restoreM_1392_);
    lean_dec_ref(v_inst_1387_);
    v___x_1393_ = lean_apply_2(v_liftWith_1391_, lean_box(0), v_f_1390_);
    v___x_1394_ = lean_apply_1(v_restoreM_1392_, lean_box(0));
    v___x_1395_ = lean_apply_4(
        v_inst_1388_,
        lean_box(0),
        lean_box(0),
        v___x_1393_,
        v___x_1394_,
    );
    return v___x_1395_;
}
pub unsafe fn l_Bind_kleisliRight___redArg(
    mut v_inst_1396_: *mut LeanObject,
    mut v_f_u2081_1397_: *mut LeanObject,
    mut v_f_u2082_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    v___x_1400_ = lean_apply_1(v_f_u2081_1397_, v_a_1399_);
    v___x_1401_ = lean_apply_4(
        v_inst_1396_,
        lean_box(0),
        lean_box(0),
        v___x_1400_,
        v_f_u2082_1398_,
    );
    return v___x_1401_;
}
pub unsafe fn l_Bind_kleisliRight(
    mut v_00_u03b1_1402_: *mut LeanObject,
    mut v_m_1403_: *mut LeanObject,
    mut v_00_u03b2_1404_: *mut LeanObject,
    mut v_00_u03b3_1405_: *mut LeanObject,
    mut v_inst_1406_: *mut LeanObject,
    mut v_f_u2081_1407_: *mut LeanObject,
    mut v_f_u2082_1408_: *mut LeanObject,
    mut v_a_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    v___x_1410_ = lean_apply_1(v_f_u2081_1407_, v_a_1409_);
    v___x_1411_ = lean_apply_4(
        v_inst_1406_,
        lean_box(0),
        lean_box(0),
        v___x_1410_,
        v_f_u2082_1408_,
    );
    return v___x_1411_;
}
pub unsafe fn l_Bind_kleisliLeft___redArg(
    mut v_inst_1412_: *mut LeanObject,
    mut v_f_u2082_1413_: *mut LeanObject,
    mut v_f_u2081_1414_: *mut LeanObject,
    mut v_a_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1416_ = lean_apply_1(v_f_u2081_1414_, v_a_1415_);
    v___x_1417_ = lean_apply_4(
        v_inst_1412_,
        lean_box(0),
        lean_box(0),
        v___x_1416_,
        v_f_u2082_1413_,
    );
    return v___x_1417_;
}
pub unsafe fn l_Bind_kleisliLeft(
    mut v_00_u03b1_1418_: *mut LeanObject,
    mut v_m_1419_: *mut LeanObject,
    mut v_00_u03b2_1420_: *mut LeanObject,
    mut v_00_u03b3_1421_: *mut LeanObject,
    mut v_inst_1422_: *mut LeanObject,
    mut v_f_u2082_1423_: *mut LeanObject,
    mut v_f_u2081_1424_: *mut LeanObject,
    mut v_a_1425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    v___x_1426_ = lean_apply_1(v_f_u2081_1424_, v_a_1425_);
    v___x_1427_ = lean_apply_4(
        v_inst_1422_,
        lean_box(0),
        lean_box(0),
        v___x_1426_,
        v_f_u2082_1423_,
    );
    return v___x_1427_;
}
pub unsafe fn l_Bind_bindLeft___redArg(
    mut v_inst_1428_: *mut LeanObject,
    mut v_f_1429_: *mut LeanObject,
    mut v_ma_1430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ = lean_apply_4(
        v_inst_1428_,
        lean_box(0),
        lean_box(0),
        v_ma_1430_,
        v_f_1429_,
    );
    return v___x_1431_;
}
pub unsafe fn l_Bind_bindLeft(
    mut v_00_u03b1_1432_: *mut LeanObject,
    mut v_m_1433_: *mut LeanObject,
    mut v_00_u03b2_1434_: *mut LeanObject,
    mut v_inst_1435_: *mut LeanObject,
    mut v_f_1436_: *mut LeanObject,
    mut v_ma_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    v___x_1438_ = lean_apply_4(
        v_inst_1435_,
        lean_box(0),
        lean_box(0),
        v_ma_1437_,
        v_f_1436_,
    );
    return v___x_1438_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1()
-> *mut LeanObject {
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    v___x_1459_ =
        l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0;
    v___x_1460_ = l_String_toRawSubstring_x27(v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(
    mut v_x_1472_: *mut LeanObject,
    mut v_a_1473_: *mut LeanObject,
    mut v_a_1474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    v___x_1475_ = l_term___x3e_x3d_x3e___00__closed__1;
    lean_inc(v_x_1472_);
    v___x_1476_ = l_Lean_Syntax_isOfKind(v_x_1472_, v___x_1475_);
    if v___x_1476_ == 0 {
        let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1472_);
        v___x_1477_ = lean_box(1);
        v___x_1478_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1478_, 0, v___x_1477_);
        lean_ctor_set(v___x_1478_, 1, v_a_1474_);
        return v___x_1478_;
    } else {
        let mut v_quotContext_1479_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1480_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1486_: u8 = 0;
        let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1479_ = lean_ctor_get(v_a_1473_, 1);
        v_currMacroScope_1480_ = lean_ctor_get(v_a_1473_, 2);
        v_ref_1481_ = lean_ctor_get(v_a_1473_, 5);
        v___x_1482_ = lean_unsigned_to_nat(0);
        v___x_1483_ = l_Lean_Syntax_getArg(v_x_1472_, v___x_1482_);
        v___x_1484_ = lean_unsigned_to_nat(2);
        v___x_1485_ = l_Lean_Syntax_getArg(v_x_1472_, v___x_1484_);
        lean_dec(v_x_1472_);
        v___x_1486_ = 0;
        v___x_1487_ = l_Lean_SourceInfo_fromRef(v_ref_1481_, v___x_1486_);
        v___x_1488_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1489_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1);
        v___x_1490_ =
            l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4;
        lean_inc(v_currMacroScope_1480_);
        lean_inc(v_quotContext_1479_);
        v___x_1491_ =
            l_Lean_addMacroScope(v_quotContext_1479_, v___x_1490_, v_currMacroScope_1480_);
        v___x_1492_ =
            l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6;
        lean_inc_n(v___x_1487_, 2);
        v___x_1493_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1493_, 0, v___x_1487_);
        lean_ctor_set(v___x_1493_, 1, v___x_1489_);
        lean_ctor_set(v___x_1493_, 2, v___x_1491_);
        lean_ctor_set(v___x_1493_, 3, v___x_1492_);
        v___x_1494_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1495_ = l_Lean_Syntax_node2(v___x_1487_, v___x_1494_, v___x_1483_, v___x_1485_);
        v___x_1496_ = l_Lean_Syntax_node2(v___x_1487_, v___x_1488_, v___x_1493_, v___x_1495_);
        v___x_1497_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1497_, 0, v___x_1496_);
        lean_ctor_set(v___x_1497_, 1, v_a_1474_);
        return v___x_1497_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___boxed(
    mut v_x_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1501_: *mut LeanObject = core::ptr::null_mut();
    v_res_1501_ = l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(
        v_x_1498_, v_a_1499_, v_a_1500_,
    );
    lean_dec_ref(v_a_1499_);
    return v_res_1501_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(
    mut v_x_1502_: *mut LeanObject,
    mut v_a_1503_: *mut LeanObject,
    mut v_a_1504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    v___x_1505_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    lean_inc(v_x_1502_);
    v___x_1506_ = l_Lean_Syntax_isOfKind(v_x_1502_, v___x_1505_);
    if v___x_1506_ == 0 {
        let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1502_);
        v___x_1507_ = lean_box(0);
        v___x_1508_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1508_, 0, v___x_1507_);
        lean_ctor_set(v___x_1508_, 1, v_a_1504_);
        return v___x_1508_;
    } else {
        let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1512_: u8 = 0;
        v___x_1509_ = lean_unsigned_to_nat(0);
        v___x_1510_ = l_Lean_Syntax_getArg(v_x_1502_, v___x_1509_);
        v___x_1511_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        lean_inc(v___x_1510_);
        v___x_1512_ = l_Lean_Syntax_isOfKind(v___x_1510_, v___x_1511_);
        if v___x_1512_ == 0 {
            let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1510_);
            lean_dec(v_x_1502_);
            v___x_1513_ = lean_box(0);
            v___x_1514_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1514_, 0, v___x_1513_);
            lean_ctor_set(v___x_1514_, 1, v_a_1504_);
            return v___x_1514_;
        } else {
            let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1518_: u8 = 0;
            v___x_1515_ = lean_unsigned_to_nat(1);
            v___x_1516_ = l_Lean_Syntax_getArg(v_x_1502_, v___x_1515_);
            lean_dec(v_x_1502_);
            v___x_1517_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1516_);
            v___x_1518_ = l_Lean_Syntax_matchesNull(v___x_1516_, v___x_1517_);
            if v___x_1518_ == 0 {
                let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1516_);
                lean_dec(v___x_1510_);
                v___x_1519_ = lean_box(0);
                v___x_1520_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                lean_ctor_set(v___x_1520_, 1, v_a_1504_);
                return v___x_1520_;
            } else {
                let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1523_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1524_: u8 = 0;
                let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
                v___x_1521_ = l_Lean_Syntax_getArg(v___x_1516_, v___x_1509_);
                v___x_1522_ = l_Lean_Syntax_getArg(v___x_1516_, v___x_1515_);
                lean_dec(v___x_1516_);
                v_ref_1523_ = l_Lean_replaceRef(v___x_1510_, v_a_1503_);
                lean_dec(v___x_1510_);
                v___x_1524_ = 0;
                v___x_1525_ = l_Lean_SourceInfo_fromRef(v_ref_1523_, v___x_1524_);
                lean_dec(v_ref_1523_);
                v___x_1526_ = l_term___x3e_x3d_x3e___00__closed__1;
                v___x_1527_ = l_term___x3e_x3d_x3e___00__closed__2;
                lean_inc(v___x_1525_);
                v___x_1528_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1528_, 0, v___x_1525_);
                lean_ctor_set(v___x_1528_, 1, v___x_1527_);
                v___x_1529_ = l_Lean_Syntax_node3(
                    v___x_1525_,
                    v___x_1526_,
                    v___x_1521_,
                    v___x_1528_,
                    v___x_1522_,
                );
                v___x_1530_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1530_, 0, v___x_1529_);
                lean_ctor_set(v___x_1530_, 1, v_a_1504_);
                return v___x_1530_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1___boxed(
    mut v_x_1531_: *mut LeanObject,
    mut v_a_1532_: *mut LeanObject,
    mut v_a_1533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1534_: *mut LeanObject = core::ptr::null_mut();
    v_res_1534_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(
        v_x_1531_, v_a_1532_, v_a_1533_,
    );
    lean_dec(v_a_1532_);
    return v_res_1534_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1()
-> *mut LeanObject {
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    v___x_1552_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0;
    v___x_1553_ = l_String_toRawSubstring_x27(v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(
    mut v_x_1564_: *mut LeanObject,
    mut v_a_1565_: *mut LeanObject,
    mut v_a_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    v___x_1567_ = l_term___x3c_x3d_x3c___00__closed__1;
    lean_inc(v_x_1564_);
    v___x_1568_ = l_Lean_Syntax_isOfKind(v_x_1564_, v___x_1567_);
    if v___x_1568_ == 0 {
        let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1564_);
        v___x_1569_ = lean_box(1);
        v___x_1570_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1570_, 0, v___x_1569_);
        lean_ctor_set(v___x_1570_, 1, v_a_1566_);
        return v___x_1570_;
    } else {
        let mut v_quotContext_1571_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1572_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: u8 = 0;
        let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1571_ = lean_ctor_get(v_a_1565_, 1);
        v_currMacroScope_1572_ = lean_ctor_get(v_a_1565_, 2);
        v_ref_1573_ = lean_ctor_get(v_a_1565_, 5);
        v___x_1574_ = lean_unsigned_to_nat(0);
        v___x_1575_ = l_Lean_Syntax_getArg(v_x_1564_, v___x_1574_);
        v___x_1576_ = lean_unsigned_to_nat(2);
        v___x_1577_ = l_Lean_Syntax_getArg(v_x_1564_, v___x_1576_);
        lean_dec(v_x_1564_);
        v___x_1578_ = 0;
        v___x_1579_ = l_Lean_SourceInfo_fromRef(v_ref_1573_, v___x_1578_);
        v___x_1580_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1581_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1);
        v___x_1582_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3;
        lean_inc(v_currMacroScope_1572_);
        lean_inc(v_quotContext_1571_);
        v___x_1583_ =
            l_Lean_addMacroScope(v_quotContext_1571_, v___x_1582_, v_currMacroScope_1572_);
        v___x_1584_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5;
        lean_inc_n(v___x_1579_, 2);
        v___x_1585_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1585_, 0, v___x_1579_);
        lean_ctor_set(v___x_1585_, 1, v___x_1581_);
        lean_ctor_set(v___x_1585_, 2, v___x_1583_);
        lean_ctor_set(v___x_1585_, 3, v___x_1584_);
        v___x_1586_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1587_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1586_, v___x_1575_, v___x_1577_);
        v___x_1588_ = l_Lean_Syntax_node2(v___x_1579_, v___x_1580_, v___x_1585_, v___x_1587_);
        v___x_1589_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1589_, 0, v___x_1588_);
        lean_ctor_set(v___x_1589_, 1, v_a_1566_);
        return v___x_1589_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___boxed(
    mut v_x_1590_: *mut LeanObject,
    mut v_a_1591_: *mut LeanObject,
    mut v_a_1592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1593_: *mut LeanObject = core::ptr::null_mut();
    v_res_1593_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(
        v_x_1590_, v_a_1591_, v_a_1592_,
    );
    lean_dec_ref(v_a_1591_);
    return v_res_1593_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(
    mut v_x_1594_: *mut LeanObject,
    mut v_a_1595_: *mut LeanObject,
    mut v_a_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: u8 = 0;
    v___x_1597_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    lean_inc(v_x_1594_);
    v___x_1598_ = l_Lean_Syntax_isOfKind(v_x_1594_, v___x_1597_);
    if v___x_1598_ == 0 {
        let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1594_);
        v___x_1599_ = lean_box(0);
        v___x_1600_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1600_, 0, v___x_1599_);
        lean_ctor_set(v___x_1600_, 1, v_a_1596_);
        return v___x_1600_;
    } else {
        let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: u8 = 0;
        v___x_1601_ = lean_unsigned_to_nat(0);
        v___x_1602_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1601_);
        v___x_1603_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        lean_inc(v___x_1602_);
        v___x_1604_ = l_Lean_Syntax_isOfKind(v___x_1602_, v___x_1603_);
        if v___x_1604_ == 0 {
            let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1602_);
            lean_dec(v_x_1594_);
            v___x_1605_ = lean_box(0);
            v___x_1606_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1606_, 0, v___x_1605_);
            lean_ctor_set(v___x_1606_, 1, v_a_1596_);
            return v___x_1606_;
        } else {
            let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1610_: u8 = 0;
            v___x_1607_ = lean_unsigned_to_nat(1);
            v___x_1608_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1607_);
            lean_dec(v_x_1594_);
            v___x_1609_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1608_);
            v___x_1610_ = l_Lean_Syntax_matchesNull(v___x_1608_, v___x_1609_);
            if v___x_1610_ == 0 {
                let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1608_);
                lean_dec(v___x_1602_);
                v___x_1611_ = lean_box(0);
                v___x_1612_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1612_, 0, v___x_1611_);
                lean_ctor_set(v___x_1612_, 1, v_a_1596_);
                return v___x_1612_;
            } else {
                let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1615_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1616_: u8 = 0;
                let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
                v___x_1613_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1601_);
                v___x_1614_ = l_Lean_Syntax_getArg(v___x_1608_, v___x_1607_);
                lean_dec(v___x_1608_);
                v_ref_1615_ = l_Lean_replaceRef(v___x_1602_, v_a_1595_);
                lean_dec(v___x_1602_);
                v___x_1616_ = 0;
                v___x_1617_ = l_Lean_SourceInfo_fromRef(v_ref_1615_, v___x_1616_);
                lean_dec(v_ref_1615_);
                v___x_1618_ = l_term___x3c_x3d_x3c___00__closed__1;
                v___x_1619_ = l_term___x3c_x3d_x3c___00__closed__2;
                lean_inc(v___x_1617_);
                v___x_1620_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1620_, 0, v___x_1617_);
                lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                v___x_1621_ = l_Lean_Syntax_node3(
                    v___x_1617_,
                    v___x_1618_,
                    v___x_1613_,
                    v___x_1620_,
                    v___x_1614_,
                );
                v___x_1622_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1622_, 0, v___x_1621_);
                lean_ctor_set(v___x_1622_, 1, v_a_1596_);
                return v___x_1622_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1___boxed(
    mut v_x_1623_: *mut LeanObject,
    mut v_a_1624_: *mut LeanObject,
    mut v_a_1625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1626_: *mut LeanObject = core::ptr::null_mut();
    v_res_1626_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(
        v_x_1623_, v_a_1624_, v_a_1625_,
    );
    lean_dec(v_a_1624_);
    return v_res_1626_;
}
pub unsafe fn _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1()
-> *mut LeanObject {
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    v___x_1644_ =
        l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0;
    v___x_1645_ = l_String_toRawSubstring_x27(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(
    mut v_x_1656_: *mut LeanObject,
    mut v_a_1657_: *mut LeanObject,
    mut v_a_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    v___x_1659_ = l_term___x3d_x3c_x3c___00__closed__1;
    lean_inc(v_x_1656_);
    v___x_1660_ = l_Lean_Syntax_isOfKind(v_x_1656_, v___x_1659_);
    if v___x_1660_ == 0 {
        let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1656_);
        v___x_1661_ = lean_box(1);
        v___x_1662_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1662_, 0, v___x_1661_);
        lean_ctor_set(v___x_1662_, 1, v_a_1658_);
        return v___x_1662_;
    } else {
        let mut v_quotContext_1663_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1664_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1670_: u8 = 0;
        let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1663_ = lean_ctor_get(v_a_1657_, 1);
        v_currMacroScope_1664_ = lean_ctor_get(v_a_1657_, 2);
        v_ref_1665_ = lean_ctor_get(v_a_1657_, 5);
        v___x_1666_ = lean_unsigned_to_nat(0);
        v___x_1667_ = l_Lean_Syntax_getArg(v_x_1656_, v___x_1666_);
        v___x_1668_ = lean_unsigned_to_nat(2);
        v___x_1669_ = l_Lean_Syntax_getArg(v_x_1656_, v___x_1668_);
        lean_dec(v_x_1656_);
        v___x_1670_ = 0;
        v___x_1671_ = l_Lean_SourceInfo_fromRef(v_ref_1665_, v___x_1670_);
        v___x_1672_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
        v___x_1673_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once), _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1);
        v___x_1674_ =
            l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3;
        lean_inc(v_currMacroScope_1664_);
        lean_inc(v_quotContext_1663_);
        v___x_1675_ =
            l_Lean_addMacroScope(v_quotContext_1663_, v___x_1674_, v_currMacroScope_1664_);
        v___x_1676_ =
            l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5;
        lean_inc_n(v___x_1671_, 2);
        v___x_1677_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1677_, 0, v___x_1671_);
        lean_ctor_set(v___x_1677_, 1, v___x_1673_);
        lean_ctor_set(v___x_1677_, 2, v___x_1675_);
        lean_ctor_set(v___x_1677_, 3, v___x_1676_);
        v___x_1678_ =
            l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13;
        v___x_1679_ = l_Lean_Syntax_node2(v___x_1671_, v___x_1678_, v___x_1667_, v___x_1669_);
        v___x_1680_ = l_Lean_Syntax_node2(v___x_1671_, v___x_1672_, v___x_1677_, v___x_1679_);
        v___x_1681_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1681_, 0, v___x_1680_);
        lean_ctor_set(v___x_1681_, 1, v_a_1658_);
        return v___x_1681_;
    }
}
pub unsafe fn l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___boxed(
    mut v_x_1682_: *mut LeanObject,
    mut v_a_1683_: *mut LeanObject,
    mut v_a_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1685_: *mut LeanObject = core::ptr::null_mut();
    v_res_1685_ = l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(
        v_x_1682_, v_a_1683_, v_a_1684_,
    );
    lean_dec_ref(v_a_1683_);
    return v_res_1685_;
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(
    mut v_x_1686_: *mut LeanObject,
    mut v_a_1687_: *mut LeanObject,
    mut v_a_1688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    v___x_1689_ =
        l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4;
    lean_inc(v_x_1686_);
    v___x_1690_ = l_Lean_Syntax_isOfKind(v_x_1686_, v___x_1689_);
    if v___x_1690_ == 0 {
        let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1686_);
        v___x_1691_ = lean_box(0);
        v___x_1692_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1692_, 0, v___x_1691_);
        lean_ctor_set(v___x_1692_, 1, v_a_1688_);
        return v___x_1692_;
    } else {
        let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1696_: u8 = 0;
        v___x_1693_ = lean_unsigned_to_nat(0);
        v___x_1694_ = l_Lean_Syntax_getArg(v_x_1686_, v___x_1693_);
        v___x_1695_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1;
        lean_inc(v___x_1694_);
        v___x_1696_ = l_Lean_Syntax_isOfKind(v___x_1694_, v___x_1695_);
        if v___x_1696_ == 0 {
            let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1694_);
            lean_dec(v_x_1686_);
            v___x_1697_ = lean_box(0);
            v___x_1698_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1698_, 0, v___x_1697_);
            lean_ctor_set(v___x_1698_, 1, v_a_1688_);
            return v___x_1698_;
        } else {
            let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1702_: u8 = 0;
            v___x_1699_ = lean_unsigned_to_nat(1);
            v___x_1700_ = l_Lean_Syntax_getArg(v_x_1686_, v___x_1699_);
            lean_dec(v_x_1686_);
            v___x_1701_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1700_);
            v___x_1702_ = l_Lean_Syntax_matchesNull(v___x_1700_, v___x_1701_);
            if v___x_1702_ == 0 {
                let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1700_);
                lean_dec(v___x_1694_);
                v___x_1703_ = lean_box(0);
                v___x_1704_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1704_, 0, v___x_1703_);
                lean_ctor_set(v___x_1704_, 1, v_a_1688_);
                return v___x_1704_;
            } else {
                let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1707_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1708_: u8 = 0;
                let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
                v___x_1705_ = l_Lean_Syntax_getArg(v___x_1700_, v___x_1693_);
                v___x_1706_ = l_Lean_Syntax_getArg(v___x_1700_, v___x_1699_);
                lean_dec(v___x_1700_);
                v_ref_1707_ = l_Lean_replaceRef(v___x_1694_, v_a_1687_);
                lean_dec(v___x_1694_);
                v___x_1708_ = 0;
                v___x_1709_ = l_Lean_SourceInfo_fromRef(v_ref_1707_, v___x_1708_);
                lean_dec(v_ref_1707_);
                v___x_1710_ = l_term___x3d_x3c_x3c___00__closed__1;
                v___x_1711_ = l_term___x3d_x3c_x3c___00__closed__2;
                lean_inc(v___x_1709_);
                v___x_1712_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1712_, 0, v___x_1709_);
                lean_ctor_set(v___x_1712_, 1, v___x_1711_);
                v___x_1713_ = l_Lean_Syntax_node3(
                    v___x_1709_,
                    v___x_1710_,
                    v___x_1705_,
                    v___x_1712_,
                    v___x_1706_,
                );
                v___x_1714_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1714_, 0, v___x_1713_);
                lean_ctor_set(v___x_1714_, 1, v_a_1688_);
                return v___x_1714_;
            }
        }
    }
}
pub unsafe fn l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1___boxed(
    mut v_x_1715_: *mut LeanObject,
    mut v_a_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1718_: *mut LeanObject = core::ptr::null_mut();
    v_res_1718_ = l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(
        v_x_1715_, v_a_1716_, v_a_1717_,
    );
    lean_dec(v_a_1716_);
    return v_res_1718_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_BinderNameHint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_BinderNameHint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_Basic(builtin);
}
