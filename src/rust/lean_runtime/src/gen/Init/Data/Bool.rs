// Lean compiler output
// Module: Init.Data.Bool
// Imports: Init.NotationExtra
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Bool_term___x5e_x5e___00__closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Bool_term___x5e_x5e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__0_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__1_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [116, 101, 114, 109, 95, 94, 94, 95, 0],
};
static mut l_Bool_term___x5e_x5e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__1_value) as *mut LeanObject;
static l_Bool_term___x5e_x5e___00__closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__0_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l_Bool_term___x5e_x5e___00__closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__1_value) as *mut LeanObject,
        10098501146595015788 as *mut LeanObject,
    ],
};
static mut l_Bool_term___x5e_x5e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__2_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__3_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Bool_term___x5e_x5e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__3_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__3_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Bool_term___x5e_x5e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__4_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__5_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 94, 94, 32, 0],
};
static mut l_Bool_term___x5e_x5e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__5_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__5_value) as *mut LeanObject],
};
static mut l_Bool_term___x5e_x5e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__6_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__7_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Bool_term___x5e_x5e___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__7_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__7_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Bool_term___x5e_x5e___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__8_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__8_value) as *mut LeanObject,
        (((34 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Bool_term___x5e_x5e___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__9_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Bool_term___x5e_x5e___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__10_value) as *mut LeanObject;
pub static l_Bool_term___x5e_x5e___00__closed__11_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__2_value) as *mut LeanObject,
        (((33 as usize) << 1) | 1) as *mut LeanObject,
        (((33 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Bool_term___x5e_x5e___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__11_value) as *mut LeanObject;
pub static mut l_Bool_term___x5e_x5e__: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__11_value) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__0_value
) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__1_value
) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__2_value
) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__3_value
) as *mut LeanObject;
static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__3_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value
) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [120, 111, 114, 0]};
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value
) as *mut LeanObject;
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value) as *mut LeanObject,5234513612094829258 as *mut LeanObject] };
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7_value
) as *mut LeanObject;
static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Bool_term___x5e_x5e___00__closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value) as *mut LeanObject,10425341760733586335 as *mut LeanObject] };
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value
) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__9_value
) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10_value) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__11_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__11_value) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__11_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12_value) as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0_value:
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
static mut l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0_value
)
    as *mut LeanObject;
pub static l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1_value:
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
            l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0_value
        ) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1_value
)
    as *mut LeanObject;
pub static mut l_Bool_instLE: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Bool_instLT: *mut LeanObject = core::ptr::null_mut();
pub static l_Bool_instMax___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Bool_instMax___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Bool_instMax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_instMax___closed__0_value) as *mut LeanObject;
pub static mut l_Bool_instMax: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_instMax___closed__0_value) as *mut LeanObject;
pub static l_Bool_instMin___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Bool_instMin___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Bool_instMin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_instMin___closed__0_value) as *mut LeanObject;
pub static mut l_Bool_instMin: *mut LeanObject =
    core::ptr::addr_of!(l_Bool_instMin___closed__0_value) as *mut LeanObject;
static mut l_Bool_toInt___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Bool_toInt___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Bool_toInt___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Bool_toInt___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Bool_xor(mut v_a_226_: u8, mut v_b_227_: u8) -> u8 {
    if v_a_226_ == 0 {
        return v_b_227_;
    } else {
        if v_b_227_ == 0 {
            return v_a_226_;
        } else {
            let mut v___x_228_: u8 = 0;
            v___x_228_ = 0;
            return v___x_228_;
        }
    }
}
pub unsafe fn l_Bool_xor___boxed(
    mut v_a_229_: *mut LeanObject,
    mut v_b_230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_231_: u8 = 0;
    let mut v_b_boxed_232_: u8 = 0;
    let mut v_res_233_: u8 = 0;
    let mut v_r_234_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_231_ = (lean_unbox(v_a_229_) as u8);
    v_b_boxed_232_ = (lean_unbox(v_b_230_) as u8);
    v_res_233_ = l_Bool_xor(v_a_boxed_231_, v_b_boxed_232_);
    v_r_234_ = lean_box((v_res_233_) as usize);
    return v_r_234_;
}
pub unsafe fn _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6()
-> *mut LeanObject {
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v___x_271_ =
        l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5;
    v___x_272_ = l_String_toRawSubstring_x27(v___x_271_);
    return v___x_272_;
}
pub unsafe fn l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(
    mut v_x_287_: *mut LeanObject,
    mut v_a_288_: *mut LeanObject,
    mut v_a_289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_291_: u8 = 0;
    v___x_290_ = l_Bool_term___x5e_x5e___00__closed__2;
    lean_inc(v_x_287_);
    v___x_291_ = l_Lean_Syntax_isOfKind(v_x_287_, v___x_290_);
    if v___x_291_ == 0 {
        let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_287_);
        v___x_292_ = lean_box(1);
        v___x_293_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_293_, 0, v___x_292_);
        lean_ctor_set(v___x_293_, 1, v_a_289_);
        return v___x_293_;
    } else {
        let mut v_quotContext_294_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_295_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_301_: u8 = 0;
        let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_294_ = lean_ctor_get(v_a_288_, 1);
        v_currMacroScope_295_ = lean_ctor_get(v_a_288_, 2);
        v_ref_296_ = lean_ctor_get(v_a_288_, 5);
        v___x_297_ = lean_unsigned_to_nat(0);
        v___x_298_ = l_Lean_Syntax_getArg(v_x_287_, v___x_297_);
        v___x_299_ = lean_unsigned_to_nat(2);
        v___x_300_ = l_Lean_Syntax_getArg(v_x_287_, v___x_299_);
        lean_dec(v_x_287_);
        v___x_301_ = 0;
        v___x_302_ = l_Lean_SourceInfo_fromRef(v_ref_296_, v___x_301_);
        v___x_303_ =
            l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4;
        v___x_304_ = lean_obj_once(core::ptr::addr_of_mut!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6), core::ptr::addr_of_mut!(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6_once), _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6);
        v___x_305_ =
            l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7;
        lean_inc(v_currMacroScope_295_);
        lean_inc(v_quotContext_294_);
        v___x_306_ = l_Lean_addMacroScope(v_quotContext_294_, v___x_305_, v_currMacroScope_295_);
        v___x_307_ =
            l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10;
        lean_inc_n(v___x_302_, 2);
        v___x_308_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_308_, 0, v___x_302_);
        lean_ctor_set(v___x_308_, 1, v___x_304_);
        lean_ctor_set(v___x_308_, 2, v___x_306_);
        lean_ctor_set(v___x_308_, 3, v___x_307_);
        v___x_309_ =
            l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12;
        v___x_310_ = l_Lean_Syntax_node2(v___x_302_, v___x_309_, v___x_298_, v___x_300_);
        v___x_311_ = l_Lean_Syntax_node2(v___x_302_, v___x_303_, v___x_308_, v___x_310_);
        v___x_312_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_312_, 0, v___x_311_);
        lean_ctor_set(v___x_312_, 1, v_a_289_);
        return v___x_312_;
    }
}
pub unsafe fn l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___boxed(
    mut v_x_313_: *mut LeanObject,
    mut v_a_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_316_: *mut LeanObject = core::ptr::null_mut();
    v_res_316_ = l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(
        v_x_313_, v_a_314_, v_a_315_,
    );
    lean_dec_ref(v_a_314_);
    return v_res_316_;
}
pub unsafe fn l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(
    mut v_x_320_: *mut LeanObject,
    mut v_a_321_: *mut LeanObject,
    mut v_a_322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: u8 = 0;
    v___x_323_ =
        l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4;
    lean_inc(v_x_320_);
    v___x_324_ = l_Lean_Syntax_isOfKind(v_x_320_, v___x_323_);
    if v___x_324_ == 0 {
        let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_320_);
        v___x_325_ = lean_box(0);
        v___x_326_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_326_, 0, v___x_325_);
        lean_ctor_set(v___x_326_, 1, v_a_322_);
        return v___x_326_;
    } else {
        let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_330_: u8 = 0;
        v___x_327_ = lean_unsigned_to_nat(0);
        v___x_328_ = l_Lean_Syntax_getArg(v_x_320_, v___x_327_);
        v___x_329_ = l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1;
        lean_inc(v___x_328_);
        v___x_330_ = l_Lean_Syntax_isOfKind(v___x_328_, v___x_329_);
        if v___x_330_ == 0 {
            let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_328_);
            lean_dec(v_x_320_);
            v___x_331_ = lean_box(0);
            v___x_332_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_332_, 0, v___x_331_);
            lean_ctor_set(v___x_332_, 1, v_a_322_);
            return v___x_332_;
        } else {
            let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_336_: u8 = 0;
            v___x_333_ = lean_unsigned_to_nat(1);
            v___x_334_ = l_Lean_Syntax_getArg(v_x_320_, v___x_333_);
            lean_dec(v_x_320_);
            v___x_335_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_334_);
            v___x_336_ = l_Lean_Syntax_matchesNull(v___x_334_, v___x_335_);
            if v___x_336_ == 0 {
                let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_334_);
                lean_dec(v___x_328_);
                v___x_337_ = lean_box(0);
                v___x_338_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_338_, 0, v___x_337_);
                lean_ctor_set(v___x_338_, 1, v_a_322_);
                return v___x_338_;
            } else {
                let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_341_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_342_: u8 = 0;
                let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
                v___x_339_ = l_Lean_Syntax_getArg(v___x_334_, v___x_327_);
                v___x_340_ = l_Lean_Syntax_getArg(v___x_334_, v___x_333_);
                lean_dec(v___x_334_);
                v_ref_341_ = l_Lean_replaceRef(v___x_328_, v_a_321_);
                lean_dec(v___x_328_);
                v___x_342_ = 0;
                v___x_343_ = l_Lean_SourceInfo_fromRef(v_ref_341_, v___x_342_);
                lean_dec(v_ref_341_);
                v___x_344_ = l_Bool_term___x5e_x5e___00__closed__2;
                v___x_345_ = l_Bool_term___x5e_x5e___00__closed__5;
                lean_inc(v___x_343_);
                v___x_346_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_346_, 0, v___x_343_);
                lean_ctor_set(v___x_346_, 1, v___x_345_);
                v___x_347_ =
                    l_Lean_Syntax_node3(v___x_343_, v___x_344_, v___x_339_, v___x_346_, v___x_340_);
                v___x_348_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_348_, 0, v___x_347_);
                lean_ctor_set(v___x_348_, 1, v_a_322_);
                return v___x_348_;
            }
        }
    }
}
pub unsafe fn l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___boxed(
    mut v_x_349_: *mut LeanObject,
    mut v_a_350_: *mut LeanObject,
    mut v_a_351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_352_: *mut LeanObject = core::ptr::null_mut();
    v_res_352_ =
        l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(v_x_349_, v_a_350_, v_a_351_);
    lean_dec(v_a_350_);
    return v_res_352_;
}
pub unsafe fn l_Bool_instDecidableForallOfDecidablePred___redArg(
    mut v_inst_353_: *mut LeanObject,
) -> u8 {
    let mut v___x_354_: u8 = 0;
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: u8 = 0;
    v___x_354_ = 1;
    v___x_355_ = lean_box((v___x_354_) as usize);
    lean_inc_ref(v_inst_353_);
    v___x_356_ = lean_apply_1(v_inst_353_, v___x_355_);
    v___x_357_ = (lean_unbox(v___x_356_) as u8);
    if v___x_357_ == 0 {
        let mut v___x_358_: u8 = 0;
        lean_dec_ref(v_inst_353_);
        v___x_358_ = (lean_unbox(v___x_356_) as u8);
        return v___x_358_;
    } else {
        let mut v___x_359_: u8 = 0;
        let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_362_: u8 = 0;
        v___x_359_ = 0;
        v___x_360_ = lean_box((v___x_359_) as usize);
        v___x_361_ = lean_apply_1(v_inst_353_, v___x_360_);
        v___x_362_ = (lean_unbox(v___x_361_) as u8);
        return v___x_362_;
    }
}
pub unsafe fn l_Bool_instDecidableForallOfDecidablePred___redArg___boxed(
    mut v_inst_363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_364_: u8 = 0;
    let mut v_r_365_: *mut LeanObject = core::ptr::null_mut();
    v_res_364_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v_inst_363_);
    v_r_365_ = lean_box((v_res_364_) as usize);
    return v_r_365_;
}
pub unsafe fn l_Bool_instDecidableForallOfDecidablePred(
    mut v_p_366_: *mut LeanObject,
    mut v_inst_367_: *mut LeanObject,
) -> u8 {
    let mut v___x_368_: u8 = 0;
    v___x_368_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v_inst_367_);
    return v___x_368_;
}
pub unsafe fn l_Bool_instDecidableForallOfDecidablePred___boxed(
    mut v_p_369_: *mut LeanObject,
    mut v_inst_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_371_: u8 = 0;
    let mut v_r_372_: *mut LeanObject = core::ptr::null_mut();
    v_res_371_ = l_Bool_instDecidableForallOfDecidablePred(v_p_369_, v_inst_370_);
    v_r_372_ = lean_box((v_res_371_) as usize);
    return v_r_372_;
}
pub unsafe fn l_Bool_instDecidableExistsOfDecidablePred___redArg(
    mut v_inst_373_: *mut LeanObject,
) -> u8 {
    let mut v___x_374_: u8 = 0;
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: u8 = 0;
    v___x_374_ = 1;
    v___x_375_ = lean_box((v___x_374_) as usize);
    lean_inc_ref(v_inst_373_);
    v___x_376_ = lean_apply_1(v_inst_373_, v___x_375_);
    v___x_377_ = (lean_unbox(v___x_376_) as u8);
    if v___x_377_ == 0 {
        let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_379_: u8 = 0;
        v___x_378_ = lean_apply_1(v_inst_373_, v___x_376_);
        v___x_379_ = (lean_unbox(v___x_378_) as u8);
        return v___x_379_;
    } else {
        let mut v___x_380_: u8 = 0;
        lean_dec_ref(v_inst_373_);
        v___x_380_ = (lean_unbox(v___x_376_) as u8);
        return v___x_380_;
    }
}
pub unsafe fn l_Bool_instDecidableExistsOfDecidablePred___redArg___boxed(
    mut v_inst_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_382_: u8 = 0;
    let mut v_r_383_: *mut LeanObject = core::ptr::null_mut();
    v_res_382_ = l_Bool_instDecidableExistsOfDecidablePred___redArg(v_inst_381_);
    v_r_383_ = lean_box((v_res_382_) as usize);
    return v_r_383_;
}
pub unsafe fn l_Bool_instDecidableExistsOfDecidablePred(
    mut v_p_384_: *mut LeanObject,
    mut v_inst_385_: *mut LeanObject,
) -> u8 {
    let mut v___x_386_: u8 = 0;
    v___x_386_ = l_Bool_instDecidableExistsOfDecidablePred___redArg(v_inst_385_);
    return v___x_386_;
}
pub unsafe fn l_Bool_instDecidableExistsOfDecidablePred___boxed(
    mut v_p_387_: *mut LeanObject,
    mut v_inst_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_389_: u8 = 0;
    let mut v_r_390_: *mut LeanObject = core::ptr::null_mut();
    v_res_389_ = l_Bool_instDecidableExistsOfDecidablePred(v_p_387_, v_inst_388_);
    v_r_390_ = lean_box((v_res_389_) as usize);
    return v_r_390_;
}
pub unsafe fn _init_l_Bool_instLE() -> *mut LeanObject {
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_box(0);
    return v___x_391_;
}
pub unsafe fn _init_l_Bool_instLT() -> *mut LeanObject {
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    v___x_392_ = lean_box(0);
    return v___x_392_;
}
pub unsafe fn l_Bool_instDecidableLe(mut v_x_393_: u8, mut v_y_394_: u8) -> u8 {
    if v_x_393_ == 0 {
        let mut v___x_395_: u8 = 0;
        v___x_395_ = 1;
        return v___x_395_;
    } else {
        return v_y_394_;
    }
}
pub unsafe fn l_Bool_instDecidableLe___boxed(
    mut v_x_396_: *mut LeanObject,
    mut v_y_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_398_: u8 = 0;
    let mut v_y_boxed_399_: u8 = 0;
    let mut v_res_400_: u8 = 0;
    let mut v_r_401_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_398_ = (lean_unbox(v_x_396_) as u8);
    v_y_boxed_399_ = (lean_unbox(v_y_397_) as u8);
    v_res_400_ = l_Bool_instDecidableLe(v_x_boxed_398_, v_y_boxed_399_);
    v_r_401_ = lean_box((v_res_400_) as usize);
    return v_r_401_;
}
pub unsafe fn l_Bool_instDecidableLt(mut v_x_402_: u8, mut v_y_403_: u8) -> u8 {
    if v_x_402_ == 0 {
        return v_y_403_;
    } else {
        let mut v___x_404_: u8 = 0;
        v___x_404_ = 0;
        return v___x_404_;
    }
}
pub unsafe fn l_Bool_instDecidableLt___boxed(
    mut v_x_405_: *mut LeanObject,
    mut v_y_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_407_: u8 = 0;
    let mut v_y_boxed_408_: u8 = 0;
    let mut v_res_409_: u8 = 0;
    let mut v_r_410_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_407_ = (lean_unbox(v_x_405_) as u8);
    v_y_boxed_408_ = (lean_unbox(v_y_406_) as u8);
    v_res_409_ = l_Bool_instDecidableLt(v_x_boxed_407_, v_y_boxed_408_);
    v_r_410_ = lean_box((v_res_409_) as usize);
    return v_r_410_;
}
pub unsafe fn l_Bool_instMax___lam__0(mut v_x_411_: u8, mut v_y_412_: u8) -> u8 {
    if v_x_411_ == 0 {
        return v_y_412_;
    } else {
        return v_x_411_;
    }
}
pub unsafe fn l_Bool_instMax___lam__0___boxed(
    mut v_x_413_: *mut LeanObject,
    mut v_y_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_415_: u8 = 0;
    let mut v_y_boxed_416_: u8 = 0;
    let mut v_res_417_: u8 = 0;
    let mut v_r_418_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_415_ = (lean_unbox(v_x_413_) as u8);
    v_y_boxed_416_ = (lean_unbox(v_y_414_) as u8);
    v_res_417_ = l_Bool_instMax___lam__0(v_x_boxed_415_, v_y_boxed_416_);
    v_r_418_ = lean_box((v_res_417_) as usize);
    return v_r_418_;
}
pub unsafe fn l_Bool_instMin___lam__0(mut v_x_421_: u8, mut v_y_422_: u8) -> u8 {
    if v_x_421_ == 0 {
        return v_x_421_;
    } else {
        return v_y_422_;
    }
}
pub unsafe fn l_Bool_instMin___lam__0___boxed(
    mut v_x_423_: *mut LeanObject,
    mut v_y_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_425_: u8 = 0;
    let mut v_y_boxed_426_: u8 = 0;
    let mut v_res_427_: u8 = 0;
    let mut v_r_428_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_425_ = (lean_unbox(v_x_423_) as u8);
    v_y_boxed_426_ = (lean_unbox(v_y_424_) as u8);
    v_res_427_ = l_Bool_instMin___lam__0(v_x_boxed_425_, v_y_boxed_426_);
    v_r_428_ = lean_box((v_res_427_) as usize);
    return v_r_428_;
}
pub unsafe fn l_Bool_toNat(mut v_b_431_: u8) -> *mut LeanObject {
    if v_b_431_ == 0 {
        let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
        v___x_432_ = lean_unsigned_to_nat(0);
        return v___x_432_;
    } else {
        let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
        v___x_433_ = lean_unsigned_to_nat(1);
        return v___x_433_;
    }
}
pub unsafe fn l_Bool_toNat___boxed(mut v_b_434_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_435_: u8 = 0;
    let mut v_res_436_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_435_ = (lean_unbox(v_b_434_) as u8);
    v_res_436_ = l_Bool_toNat(v_b_boxed_435_);
    return v_res_436_;
}
pub unsafe fn _init_l_Bool_toInt___closed__0() -> *mut LeanObject {
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    v___x_437_ = lean_unsigned_to_nat(0);
    v___x_438_ = lean_nat_to_int(v___x_437_);
    return v___x_438_;
}
pub unsafe fn _init_l_Bool_toInt___closed__1() -> *mut LeanObject {
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v___x_439_ = lean_unsigned_to_nat(1);
    v___x_440_ = lean_nat_to_int(v___x_439_);
    return v___x_440_;
}
pub unsafe fn l_Bool_toInt(mut v_b_441_: u8) -> *mut LeanObject {
    if v_b_441_ == 0 {
        let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
        v___x_442_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Bool_toInt___closed__0),
            core::ptr::addr_of_mut!(l_Bool_toInt___closed__0_once),
            _init_l_Bool_toInt___closed__0,
        );
        return v___x_442_;
    } else {
        let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
        v___x_443_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Bool_toInt___closed__1),
            core::ptr::addr_of_mut!(l_Bool_toInt___closed__1_once),
            _init_l_Bool_toInt___closed__1,
        );
        return v___x_443_;
    }
}
pub unsafe fn l_Bool_toInt___boxed(mut v_b_444_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_445_: u8 = 0;
    let mut v_res_446_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_445_ = (lean_unbox(v_b_444_) as u8);
    v_res_446_ = l_Bool_toInt(v_b_boxed_445_);
    return v_res_446_;
}
pub unsafe fn l_boolPredToPred(mut v_00_u03b1_447_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    v___x_448_ = lean_box(0);
    return v___x_448_;
}
pub unsafe fn l_boolRelToRel(mut v_00_u03b1_449_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    v___x_450_ = lean_box(0);
    return v___x_450_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Bool(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Bool_instLE = _init_l_Bool_instLE();
    lean_mark_persistent(l_Bool_instLE);
    l_Bool_instLT = _init_l_Bool_instLT();
    lean_mark_persistent(l_Bool_instLT);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Bool(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Bool(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Bool(builtin);
}
