// Lean compiler output
// Module: Init.Data.List.BasicAux
// Imports: Init.GetElem Init.WFTactics Init.ByCases Init.Classical Init.Data.Array.Basic Init.Data.Nat.Linear
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::List::Basic::l_List_getLast___redArg;
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::GetElem::{
    initialize_Init_GetElem, l_List_get_x3fInternal___redArg, runtime_initialize_Init_GetElem,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_List_getLast_x21___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99,
        65, 117, 120, 0,
    ],
};
static mut l_List_getLast_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_getLast_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_getLast_x21___redArg___closed__1_value: LeanStringObject<14> = LeanStringObject {
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
        76, 105, 115, 116, 46, 103, 101, 116, 76, 97, 115, 116, 33, 0,
    ],
};
static mut l_List_getLast_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_getLast_x21___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_getLast_x21___redArg___closed__2_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [101, 109, 112, 116, 121, 32, 108, 105, 115, 116, 0],
};
static mut l_List_getLast_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_List_getLast_x21___redArg___closed__2_value) as *mut LeanObject;
static mut l_List_getLast_x21___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_getLast_x21___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_List_head_x21___redArg___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [76, 105, 115, 116, 46, 104, 101, 97, 100, 33, 0],
};
static mut l_List_head_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_head_x21___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_head_x21___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_head_x21___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_tail_x21___redArg___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [76, 105, 115, 116, 46, 116, 97, 105, 108, 33, 0],
};
static mut l_List_tail_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_tail_x21___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_tail_x21___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_tail_x21___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_partitionM___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_List_partitionM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_partitionM___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_tacticSizeOf__list__dec___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 105, 115, 116, 0],
    };
static mut l_List_tacticSizeOf__list__dec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__0_value) as *mut LeanObject;
pub static l_List_tacticSizeOf__list__dec___closed__1_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            116, 97, 99, 116, 105, 99, 83, 105, 122, 101, 79, 102, 95, 108, 105, 115, 116, 95, 100,
            101, 99, 0,
        ],
    };
static mut l_List_tacticSizeOf__list__dec___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__1_value) as *mut LeanObject;
static l_List_tacticSizeOf__list__dec___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__0_value) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_List_tacticSizeOf__list__dec___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__1_value) as *mut LeanObject,
        3080047469881858702 as *mut LeanObject,
    ],
};
static mut l_List_tacticSizeOf__list__dec___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__2_value) as *mut LeanObject;
pub static l_List_tacticSizeOf__list__dec___closed__3_value: LeanStringObject<16> =
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
            115, 105, 122, 101, 79, 102, 95, 108, 105, 115, 116, 95, 100, 101, 99, 0,
        ],
    };
static mut l_List_tacticSizeOf__list__dec___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__3_value) as *mut LeanObject;
pub static l_List_tacticSizeOf__list__dec___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__3_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_List_tacticSizeOf__list__dec___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__4_value) as *mut LeanObject;
pub static l_List_tacticSizeOf__list__dec___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__2_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_List_tacticSizeOf__list__dec___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__5_value) as *mut LeanObject;
pub static mut l_List_tacticSizeOf__list__dec: *mut LeanObject =
    core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__5_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 114, 115, 116, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3_value) as *mut LeanObject,12551601070224435259 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__5_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__5_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__6_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__7_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__7_value) as *mut LeanObject,2214559063752339918 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__8_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__9_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__9_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__10_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__10_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__12_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__12_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__12_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__14_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__14_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__14_value) as *mut LeanObject,6022092293134036165 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__16_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__16_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17_value) as *mut LeanObject,5826123769708379594 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 79, 102, 95, 108, 116, 95, 111, 102, 95, 109, 101, 109, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19_value) as *mut LeanObject;
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19_value) as *mut LeanObject,2615829501118115902 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__21_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__0_value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19_value) as *mut LeanObject,1795713974869802024 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__23_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__23_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__24_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__23_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__24_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__25_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__25_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26_value) as *mut LeanObject,16687334436616221424 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 110, 101, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28_value) as *mut LeanObject,8876691400619696497 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__31_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__31_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__31_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__33_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [78, 97, 116, 46, 108, 116, 95, 111, 102, 95, 108, 116, 95, 111, 102, 95, 108, 101, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__33_value) as *mut LeanObject;
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34: *mut LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__35_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__35_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__36_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [108, 116, 95, 111, 102, 95, 108, 116, 95, 111, 102, 95, 108, 101, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__36: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__36_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__35_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__36_value) as *mut LeanObject,16353715261002541318 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__38_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__38: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__38_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__39_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__38_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__39: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__39_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__40_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__40: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__40_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__40_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__42_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__42: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__42_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__42_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__44_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__44: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__44_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__45_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__45: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__45_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__46_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__45_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__46: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__46_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__47_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__47: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__47_value) as *mut LeanObject;
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48: *mut LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__49_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_tacticSizeOf__list__dec___closed__0_value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__49: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__49_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__50_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__49_value) as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__50: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__50_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__51_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__50_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__51: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__51_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__52_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__52: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__52_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__52_value) as *mut LeanObject,11921244625177918938 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__54_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__54: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__54_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55_value) as *mut LeanObject;
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56: *mut LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__57_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55_value) as *mut LeanObject,8738205681931236784 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__57: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__57_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__58_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__58: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__58_value) as *mut LeanObject;
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59: *mut LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 39, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60_value) as *mut LeanObject,7640173075534255494 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__62_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 65, 114, 103, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__62: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__62_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__62_value) as *mut LeanObject,14546932361418667927 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__64_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__64: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__64_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__64_value) as *mut LeanObject,13771926289831477797 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__66_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__66: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__66_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67_value) as *mut LeanObject,12783917532758215986 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__69_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__69: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__69_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__69_value) as *mut LeanObject,3488656302031949961 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__71_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__71: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__71_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__71_value) as *mut LeanObject,10138443044734372301 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__73_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 111, 115, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__73: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__73_value) as *mut LeanObject;
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__73_value) as *mut LeanObject,9555431800314169832 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__75_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [43, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__75: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__75_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 105, 116, 104, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76_value) as *mut LeanObject;
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77: *mut LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__78_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76_value) as *mut LeanObject,3738010876686032200 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__78: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__78_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114, 105, 118, 105, 97, 108, 0]};
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut LeanObject;
pub static l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut LeanObject,5744670087858236374 as *mut LeanObject] };
static mut l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_List_getD___redArg(
    mut v_as_702_: *mut LeanObject,
    mut v_i_703_: *mut LeanObject,
    mut v_fallback_704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    v___x_705_ = l_List_get_x3fInternal___redArg(v_as_702_, v_i_703_);
    if lean_obj_tag(v___x_705_) == 0 {
        lean_inc(v_fallback_704_);
        return v_fallback_704_;
    } else {
        let mut v_val_706_: *mut LeanObject = core::ptr::null_mut();
        v_val_706_ = lean_ctor_get(v___x_705_, 0);
        lean_inc(v_val_706_);
        lean_dec_ref_known(v___x_705_, 1);
        return v_val_706_;
    }
}
pub unsafe fn l_List_getD___redArg___boxed(
    mut v_as_707_: *mut LeanObject,
    mut v_i_708_: *mut LeanObject,
    mut v_fallback_709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_710_: *mut LeanObject = core::ptr::null_mut();
    v_res_710_ = l_List_getD___redArg(v_as_707_, v_i_708_, v_fallback_709_);
    lean_dec(v_fallback_709_);
    lean_dec(v_as_707_);
    return v_res_710_;
}
pub unsafe fn l_List_getD(
    mut v_00_u03b1_711_: *mut LeanObject,
    mut v_as_712_: *mut LeanObject,
    mut v_i_713_: *mut LeanObject,
    mut v_fallback_714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    v___x_715_ = l_List_getD___redArg(v_as_712_, v_i_713_, v_fallback_714_);
    return v___x_715_;
}
pub unsafe fn l_List_getD___boxed(
    mut v_00_u03b1_716_: *mut LeanObject,
    mut v_as_717_: *mut LeanObject,
    mut v_i_718_: *mut LeanObject,
    mut v_fallback_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_720_: *mut LeanObject = core::ptr::null_mut();
    v_res_720_ = l_List_getD(v_00_u03b1_716_, v_as_717_, v_i_718_, v_fallback_719_);
    lean_dec(v_fallback_719_);
    lean_dec(v_as_717_);
    return v_res_720_;
}
pub unsafe fn _init_l_List_getLast_x21___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    v___x_724_ = l_List_getLast_x21___redArg___closed__2;
    v___x_725_ = lean_unsigned_to_nat(13);
    v___x_726_ = lean_unsigned_to_nat(64);
    v___x_727_ = l_List_getLast_x21___redArg___closed__1;
    v___x_728_ = l_List_getLast_x21___redArg___closed__0;
    v___x_729_ =
        l_mkPanicMessageWithDecl(v___x_728_, v___x_727_, v___x_726_, v___x_725_, v___x_724_);
    return v___x_729_;
}
pub unsafe fn l_List_getLast_x21___redArg(
    mut v_inst_730_: *mut LeanObject,
    mut v_x_731_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_731_) == 0 {
        let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
        v___x_732_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_List_getLast_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_List_getLast_x21___redArg___closed__3_once),
            _init_l_List_getLast_x21___redArg___closed__3,
        );
        v___x_733_ = l_panic___redArg(v_inst_730_, v___x_732_);
        return v___x_733_;
    } else {
        let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
        v___x_734_ = l_List_getLast___redArg(v_x_731_);
        return v___x_734_;
    }
}
pub unsafe fn l_List_getLast_x21___redArg___boxed(
    mut v_inst_735_: *mut LeanObject,
    mut v_x_736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_737_: *mut LeanObject = core::ptr::null_mut();
    v_res_737_ = l_List_getLast_x21___redArg(v_inst_735_, v_x_736_);
    lean_dec(v_x_736_);
    lean_dec(v_inst_735_);
    return v_res_737_;
}
pub unsafe fn l_List_getLast_x21(
    mut v_00_u03b1_738_: *mut LeanObject,
    mut v_inst_739_: *mut LeanObject,
    mut v_x_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    v___x_741_ = l_List_getLast_x21___redArg(v_inst_739_, v_x_740_);
    return v___x_741_;
}
pub unsafe fn l_List_getLast_x21___boxed(
    mut v_00_u03b1_742_: *mut LeanObject,
    mut v_inst_743_: *mut LeanObject,
    mut v_x_744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_745_: *mut LeanObject = core::ptr::null_mut();
    v_res_745_ = l_List_getLast_x21(v_00_u03b1_742_, v_inst_743_, v_x_744_);
    lean_dec(v_x_744_);
    lean_dec(v_inst_743_);
    return v_res_745_;
}
pub unsafe fn _init_l_List_head_x21___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    v___x_747_ = l_List_getLast_x21___redArg___closed__2;
    v___x_748_ = lean_unsigned_to_nat(12);
    v___x_749_ = lean_unsigned_to_nat(80);
    v___x_750_ = l_List_head_x21___redArg___closed__0;
    v___x_751_ = l_List_getLast_x21___redArg___closed__0;
    v___x_752_ =
        l_mkPanicMessageWithDecl(v___x_751_, v___x_750_, v___x_749_, v___x_748_, v___x_747_);
    return v___x_752_;
}
pub unsafe fn l_List_head_x21___redArg(
    mut v_inst_753_: *mut LeanObject,
    mut v_x_754_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_754_) == 0 {
        let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
        v___x_755_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_List_head_x21___redArg___closed__1),
            core::ptr::addr_of_mut!(l_List_head_x21___redArg___closed__1_once),
            _init_l_List_head_x21___redArg___closed__1,
        );
        v___x_756_ = l_panic___redArg(v_inst_753_, v___x_755_);
        return v___x_756_;
    } else {
        let mut v_head_757_: *mut LeanObject = core::ptr::null_mut();
        v_head_757_ = lean_ctor_get(v_x_754_, 0);
        lean_inc(v_head_757_);
        return v_head_757_;
    }
}
pub unsafe fn l_List_head_x21___redArg___boxed(
    mut v_inst_758_: *mut LeanObject,
    mut v_x_759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_760_: *mut LeanObject = core::ptr::null_mut();
    v_res_760_ = l_List_head_x21___redArg(v_inst_758_, v_x_759_);
    lean_dec(v_x_759_);
    lean_dec(v_inst_758_);
    return v_res_760_;
}
pub unsafe fn l_List_head_x21(
    mut v_00_u03b1_761_: *mut LeanObject,
    mut v_inst_762_: *mut LeanObject,
    mut v_x_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    v___x_764_ = l_List_head_x21___redArg(v_inst_762_, v_x_763_);
    return v___x_764_;
}
pub unsafe fn l_List_head_x21___boxed(
    mut v_00_u03b1_765_: *mut LeanObject,
    mut v_inst_766_: *mut LeanObject,
    mut v_x_767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_768_: *mut LeanObject = core::ptr::null_mut();
    v_res_768_ = l_List_head_x21(v_00_u03b1_765_, v_inst_766_, v_x_767_);
    lean_dec(v_x_767_);
    lean_dec(v_inst_766_);
    return v_res_768_;
}
pub unsafe fn l_panic___at___00List_tail_x21_spec__0___redArg(
    mut v_msg_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    v___x_770_ = lean_box(0);
    v___x_771_ = lean_panic_fn_borrowed(v___x_770_, v_msg_769_);
    return v___x_771_;
}
pub unsafe fn l_panic___at___00List_tail_x21_spec__0(
    mut v_00_u03b1_772_: *mut LeanObject,
    mut v_msg_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    v___x_774_ = l_panic___at___00List_tail_x21_spec__0___redArg(v_msg_773_);
    return v___x_774_;
}
pub unsafe fn _init_l_List_tail_x21___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    v___x_776_ = l_List_getLast_x21___redArg___closed__2;
    v___x_777_ = lean_unsigned_to_nat(13);
    v___x_778_ = lean_unsigned_to_nat(99);
    v___x_779_ = l_List_tail_x21___redArg___closed__0;
    v___x_780_ = l_List_getLast_x21___redArg___closed__0;
    v___x_781_ =
        l_mkPanicMessageWithDecl(v___x_780_, v___x_779_, v___x_778_, v___x_777_, v___x_776_);
    return v___x_781_;
}
pub unsafe fn l_List_tail_x21___redArg(mut v_x_782_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_782_) == 0 {
        let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
        v___x_783_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_List_tail_x21___redArg___closed__1),
            core::ptr::addr_of_mut!(l_List_tail_x21___redArg___closed__1_once),
            _init_l_List_tail_x21___redArg___closed__1,
        );
        v___x_784_ = l_panic___at___00List_tail_x21_spec__0___redArg(v___x_783_);
        return v___x_784_;
    } else {
        let mut v_tail_785_: *mut LeanObject = core::ptr::null_mut();
        v_tail_785_ = lean_ctor_get(v_x_782_, 1);
        lean_inc(v_tail_785_);
        return v_tail_785_;
    }
}
pub unsafe fn l_List_tail_x21___redArg___boxed(mut v_x_786_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_787_: *mut LeanObject = core::ptr::null_mut();
    v_res_787_ = l_List_tail_x21___redArg(v_x_786_);
    lean_dec(v_x_786_);
    return v_res_787_;
}
pub unsafe fn l_List_tail_x21(
    mut v_00_u03b1_788_: *mut LeanObject,
    mut v_x_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    v___x_790_ = l_List_tail_x21___redArg(v_x_789_);
    return v___x_790_;
}
pub unsafe fn l_List_tail_x21___boxed(
    mut v_00_u03b1_791_: *mut LeanObject,
    mut v_x_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_793_: *mut LeanObject = core::ptr::null_mut();
    v_res_793_ = l_List_tail_x21(v_00_u03b1_791_, v_x_792_);
    lean_dec(v_x_792_);
    return v_res_793_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0___boxed(
    mut v_a_794_: *mut LeanObject,
    mut v_head_795_: *mut LeanObject,
    mut v_inst_796_: *mut LeanObject,
    mut v_p_797_: *mut LeanObject,
    mut v_tail_798_: *mut LeanObject,
    mut v_a_799_: *mut LeanObject,
    mut v_____do__lift_800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_97__boxed_801_: u8 = 0;
    let mut v_res_802_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_97__boxed_801_ = (lean_unbox(v_____do__lift_800_) as u8);
    v_res_802_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0(
        v_a_794_,
        v_head_795_,
        v_inst_796_,
        v_p_797_,
        v_tail_798_,
        v_a_799_,
        v_____do__lift_97__boxed_801_,
    );
    return v_res_802_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(
    mut v_inst_803_: *mut LeanObject,
    mut v_p_804_: *mut LeanObject,
    mut v_a_805_: *mut LeanObject,
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_811_: u8 = 0;
    let mut v_toPure_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_819_: u8 = 0;
    let mut v_unused_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_805_) == 0 {
                    v_toApplicative_808_ = lean_ctor_get(v_inst_803_, 0);
                    lean_inc_ref(v_toApplicative_808_);
                    lean_dec(v_p_804_);
                    v_isSharedCheck_819_ = (!lean_is_exclusive(v_inst_803_)) as u8;
                    if v_isSharedCheck_819_ == 0 {
                        v_unused_820_ = lean_ctor_get(v_inst_803_, 1);
                        lean_dec(v_unused_820_);
                        v_unused_821_ = lean_ctor_get(v_inst_803_, 0);
                        lean_dec(v_unused_821_);
                        v___x_810_ = v_inst_803_;
                        v_isShared_811_ = v_isSharedCheck_819_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_inst_803_);
                        v___x_810_ = lean_box(0);
                        v_isShared_811_ = v_isSharedCheck_819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_toBind_822_ = lean_ctor_get(v_inst_803_, 1);
                    lean_inc(v_toBind_822_);
                    v_head_823_ = lean_ctor_get(v_a_805_, 0);
                    lean_inc_n(v_head_823_, 2);
                    v_tail_824_ = lean_ctor_get(v_a_805_, 1);
                    lean_inc(v_tail_824_);
                    lean_dec_ref_known(v_a_805_, 2);
                    lean_inc(v_p_804_);
                    v___f_825_ = lean_alloc_closure(l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 6);
                    lean_closure_set(v___f_825_, 0, v_a_807_);
                    lean_closure_set(v___f_825_, 1, v_head_823_);
                    lean_closure_set(v___f_825_, 2, v_inst_803_);
                    lean_closure_set(v___f_825_, 3, v_p_804_);
                    lean_closure_set(v___f_825_, 4, v_tail_824_);
                    lean_closure_set(v___f_825_, 5, v_a_806_);
                    v___x_826_ = lean_apply_1(v_p_804_, v_head_823_);
                    v___x_827_ = lean_apply_4(
                        v_toBind_822_,
                        lean_box(0),
                        lean_box(0),
                        v___x_826_,
                        v___f_825_,
                    );
                    return v___x_827_;
                }
            }
            1 => {
                v_toPure_812_ = lean_ctor_get(v_toApplicative_808_, 1);
                lean_inc(v_toPure_812_);
                lean_dec_ref(v_toApplicative_808_);
                v___x_813_ = lean_array_to_list(v_a_806_);
                v___x_814_ = lean_array_to_list(v_a_807_);
                if v_isShared_811_ == 0 {
                    lean_ctor_set(v___x_810_, 1, v___x_814_);
                    lean_ctor_set(v___x_810_, 0, v___x_813_);
                    v___x_816_ = v___x_810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_813_);
                    lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_814_);
                    v___x_816_ = v_reuseFailAlloc_818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_817_ = lean_apply_2(v_toPure_812_, lean_box(0), v___x_816_);
                return v___x_817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0(
    mut v_a_828_: *mut LeanObject,
    mut v_head_829_: *mut LeanObject,
    mut v_inst_830_: *mut LeanObject,
    mut v_p_831_: *mut LeanObject,
    mut v_tail_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
    mut v_____do__lift_834_: u8,
) -> *mut LeanObject {
    if v_____do__lift_834_ == 0 {
        let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
        v___x_835_ = lean_array_push(v_a_828_, v_head_829_);
        v___x_836_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(
            v_inst_830_,
            v_p_831_,
            v_tail_832_,
            v_a_833_,
            v___x_835_,
        );
        return v___x_836_;
    } else {
        let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
        v___x_837_ = lean_array_push(v_a_833_, v_head_829_);
        v___x_838_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(
            v_inst_830_,
            v_p_831_,
            v_tail_832_,
            v___x_837_,
            v_a_828_,
        );
        return v___x_838_;
    }
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_partitionM_go(
    mut v_m_839_: *mut LeanObject,
    mut v_00_u03b1_840_: *mut LeanObject,
    mut v_inst_841_: *mut LeanObject,
    mut v_p_842_: *mut LeanObject,
    mut v_a_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    v___x_846_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(
        v_inst_841_,
        v_p_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
    );
    return v___x_846_;
}
pub unsafe fn l_List_partitionM___redArg(
    mut v_inst_849_: *mut LeanObject,
    mut v_p_850_: *mut LeanObject,
    mut v_l_851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    v___x_852_ = l_List_partitionM___redArg___closed__0;
    v___x_853_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(
        v_inst_849_,
        v_p_850_,
        v_l_851_,
        v___x_852_,
        v___x_852_,
    );
    return v___x_853_;
}
pub unsafe fn l_List_partitionM(
    mut v_m_854_: *mut LeanObject,
    mut v_00_u03b1_855_: *mut LeanObject,
    mut v_inst_856_: *mut LeanObject,
    mut v_p_857_: *mut LeanObject,
    mut v_l_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    v___x_859_ = l_List_partitionM___redArg___closed__0;
    v___x_860_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(
        v_inst_856_,
        v_p_857_,
        v_l_858_,
        v___x_859_,
        v___x_859_,
    );
    return v___x_860_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_partitionMap_go___redArg(
    mut v_f_861_: *mut LeanObject,
    mut v_a_862_: *mut LeanObject,
    mut v_a_863_: *mut LeanObject,
    mut v_a_864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_862_) == 0 {
                    lean_dec_ref(v_f_861_);
                    v___x_865_ = lean_array_to_list(v_a_863_);
                    v___x_866_ = lean_array_to_list(v_a_864_);
                    v___x_867_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_867_, 0, v___x_865_);
                    lean_ctor_set(v___x_867_, 1, v___x_866_);
                    return v___x_867_;
                } else {
                    v_head_868_ = lean_ctor_get(v_a_862_, 0);
                    lean_inc(v_head_868_);
                    v_tail_869_ = lean_ctor_get(v_a_862_, 1);
                    lean_inc(v_tail_869_);
                    lean_dec_ref_known(v_a_862_, 2);
                    lean_inc_ref(v_f_861_);
                    v___x_870_ = lean_apply_1(v_f_861_, v_head_868_);
                    if lean_obj_tag(v___x_870_) == 0 {
                        v_val_871_ = lean_ctor_get(v___x_870_, 0);
                        lean_inc(v_val_871_);
                        lean_dec_ref_known(v___x_870_, 1);
                        v___x_872_ = lean_array_push(v_a_863_, v_val_871_);
                        v_a_862_ = v_tail_869_;
                        v_a_863_ = v___x_872_;
                        state = 0;
                        continue;
                    } else {
                        v_val_874_ = lean_ctor_get(v___x_870_, 0);
                        lean_inc(v_val_874_);
                        lean_dec_ref_known(v___x_870_, 1);
                        v___x_875_ = lean_array_push(v_a_864_, v_val_874_);
                        v_a_862_ = v_tail_869_;
                        v_a_864_ = v___x_875_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_partitionMap_go(
    mut v_00_u03b1_877_: *mut LeanObject,
    mut v_00_u03b2_878_: *mut LeanObject,
    mut v_00_u03b3_879_: *mut LeanObject,
    mut v_f_880_: *mut LeanObject,
    mut v_a_881_: *mut LeanObject,
    mut v_a_882_: *mut LeanObject,
    mut v_a_883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    v___x_884_ = l___private_Init_Data_List_BasicAux_0__List_partitionMap_go___redArg(
        v_f_880_, v_a_881_, v_a_882_, v_a_883_,
    );
    return v___x_884_;
}
pub unsafe fn l_List_partitionMap___redArg(
    mut v_f_885_: *mut LeanObject,
    mut v_l_886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_887_ = l_List_partitionM___redArg___closed__0;
    v___x_888_ = l___private_Init_Data_List_BasicAux_0__List_partitionMap_go___redArg(
        v_f_885_, v_l_886_, v___x_887_, v___x_887_,
    );
    return v___x_888_;
}
pub unsafe fn l_List_partitionMap(
    mut v_00_u03b1_889_: *mut LeanObject,
    mut v_00_u03b2_890_: *mut LeanObject,
    mut v_00_u03b3_891_: *mut LeanObject,
    mut v_f_892_: *mut LeanObject,
    mut v_l_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    v___x_894_ = l_List_partitionM___redArg___closed__0;
    v___x_895_ = l___private_Init_Data_List_BasicAux_0__List_partitionMap_go___redArg(
        v_f_892_, v_l_893_, v___x_894_, v___x_894_,
    );
    return v___x_895_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0(
    mut v_b_x27_896_: *mut LeanObject,
    mut v_toPure_897_: *mut LeanObject,
    mut v_as_898_: *mut LeanObject,
    mut v_head_899_: *mut LeanObject,
    mut v_tail_900_: *mut LeanObject,
    mut v_bs_x27_901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_903_: u8 = 0;
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: usize = 0;
    let mut v___x_908_: usize = 0;
    let mut v___x_909_: u8 = 0;
    let mut v___x_910_: usize = 0;
    let mut v___x_911_: usize = 0;
    let mut v___x_912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_907_ = lean_ptr_addr(v_b_x27_896_);
                v___x_908_ = lean_ptr_addr(v_head_899_);
                v___x_909_ = lean_usize_dec_eq(v___x_907_, v___x_908_);
                if v___x_909_ == 0 {
                    v___y_903_ = v___x_909_;
                    state = 1;
                    continue;
                } else {
                    v___x_910_ = lean_ptr_addr(v_bs_x27_901_);
                    v___x_911_ = lean_ptr_addr(v_tail_900_);
                    v___x_912_ = lean_usize_dec_eq(v___x_910_, v___x_911_);
                    v___y_903_ = v___x_912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_903_ == 0 {
                    lean_dec(v_as_898_);
                    v___x_904_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_904_, 0, v_b_x27_896_);
                    lean_ctor_set(v___x_904_, 1, v_bs_x27_901_);
                    v___x_905_ = lean_apply_2(v_toPure_897_, lean_box(0), v___x_904_);
                    return v___x_905_;
                } else {
                    lean_dec(v_bs_x27_901_);
                    lean_dec(v_b_x27_896_);
                    v___x_906_ = lean_apply_2(v_toPure_897_, lean_box(0), v_as_898_);
                    return v___x_906_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0___boxed(
    mut v_b_x27_913_: *mut LeanObject,
    mut v_toPure_914_: *mut LeanObject,
    mut v_as_915_: *mut LeanObject,
    mut v_head_916_: *mut LeanObject,
    mut v_tail_917_: *mut LeanObject,
    mut v_bs_x27_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_919_: *mut LeanObject = core::ptr::null_mut();
    v_res_919_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0(
        v_b_x27_913_,
        v_toPure_914_,
        v_as_915_,
        v_head_916_,
        v_tail_917_,
        v_bs_x27_918_,
    );
    lean_dec(v_tail_917_);
    lean_dec(v_head_916_);
    return v_res_919_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg(
    mut v_inst_920_: *mut LeanObject,
    mut v_as_921_: *mut LeanObject,
    mut v_f_922_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_as_921_) == 0 {
        let mut v_toApplicative_923_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_924_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_923_ = lean_ctor_get(v_inst_920_, 0);
        lean_inc_ref(v_toApplicative_923_);
        lean_dec(v_f_922_);
        lean_dec_ref(v_inst_920_);
        v_toPure_924_ = lean_ctor_get(v_toApplicative_923_, 1);
        lean_inc(v_toPure_924_);
        lean_dec_ref(v_toApplicative_923_);
        v___x_925_ = lean_apply_2(v_toPure_924_, lean_box(0), v_as_921_);
        return v___x_925_;
    } else {
        let mut v_toApplicative_926_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_927_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_928_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_929_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_926_ = lean_ctor_get(v_inst_920_, 0);
        v_toBind_927_ = lean_ctor_get(v_inst_920_, 1);
        lean_inc_n(v_toBind_927_, 2);
        v_toPure_928_ = lean_ctor_get(v_toApplicative_926_, 1);
        lean_inc(v_toPure_928_);
        v_head_929_ = lean_ctor_get(v_as_921_, 0);
        lean_inc_n(v_head_929_, 2);
        v_tail_930_ = lean_ctor_get(v_as_921_, 1);
        lean_inc(v_tail_930_);
        lean_inc(v_f_922_);
        v___f_931_ = lean_alloc_closure(
            l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__1
                as *mut core::ffi::c_void,
            8,
            7,
        );
        lean_closure_set(v___f_931_, 0, v_toPure_928_);
        lean_closure_set(v___f_931_, 1, v_as_921_);
        lean_closure_set(v___f_931_, 2, v_head_929_);
        lean_closure_set(v___f_931_, 3, v_tail_930_);
        lean_closure_set(v___f_931_, 4, v_inst_920_);
        lean_closure_set(v___f_931_, 5, v_f_922_);
        lean_closure_set(v___f_931_, 6, v_toBind_927_);
        v___x_932_ = lean_apply_1(v_f_922_, v_head_929_);
        v___x_933_ = lean_apply_4(
            v_toBind_927_,
            lean_box(0),
            lean_box(0),
            v___x_932_,
            v___f_931_,
        );
        return v___x_933_;
    }
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__1(
    mut v_toPure_934_: *mut LeanObject,
    mut v_as_935_: *mut LeanObject,
    mut v_head_936_: *mut LeanObject,
    mut v_tail_937_: *mut LeanObject,
    mut v_inst_938_: *mut LeanObject,
    mut v_f_939_: *mut LeanObject,
    mut v_toBind_940_: *mut LeanObject,
    mut v_b_x27_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_tail_937_);
    v___f_942_ = lean_alloc_closure(
        l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_942_, 0, v_b_x27_941_);
    lean_closure_set(v___f_942_, 1, v_toPure_934_);
    lean_closure_set(v___f_942_, 2, v_as_935_);
    lean_closure_set(v___f_942_, 3, v_head_936_);
    lean_closure_set(v___f_942_, 4, v_tail_937_);
    v___x_943_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg(
        v_inst_938_,
        v_tail_937_,
        v_f_939_,
    );
    v___x_944_ = lean_apply_4(
        v_toBind_940_,
        lean_box(0),
        lean_box(0),
        v___x_943_,
        v___f_942_,
    );
    return v___x_944_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp(
    mut v_m_945_: *mut LeanObject,
    mut v_00_u03b1_946_: *mut LeanObject,
    mut v_inst_947_: *mut LeanObject,
    mut v_as_948_: *mut LeanObject,
    mut v_f_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    v___x_950_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg(
        v_inst_947_,
        v_as_948_,
        v_f_949_,
    );
    return v___x_950_;
}
pub unsafe fn l_List_mapMonoM___redArg___lam__0(
    mut v_____do__lift_951_: *mut LeanObject,
    mut v_toPure_952_: *mut LeanObject,
    mut v_____do__lift_953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    v___x_954_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_954_, 0, v_____do__lift_951_);
    lean_ctor_set(v___x_954_, 1, v_____do__lift_953_);
    v___x_955_ = lean_apply_2(v_toPure_952_, lean_box(0), v___x_954_);
    return v___x_955_;
}
pub unsafe fn l_List_mapMonoM___redArg___lam__1(
    mut v_toPure_956_: *mut LeanObject,
    mut v_inst_957_: *mut LeanObject,
    mut v_tail_958_: *mut LeanObject,
    mut v_f_959_: *mut LeanObject,
    mut v_toBind_960_: *mut LeanObject,
    mut v_____do__lift_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    v___f_962_ = lean_alloc_closure(
        l_List_mapMonoM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_962_, 0, v_____do__lift_961_);
    lean_closure_set(v___f_962_, 1, v_toPure_956_);
    v___x_963_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg(
        v_inst_957_,
        v_tail_958_,
        v_f_959_,
    );
    v___x_964_ = lean_apply_4(
        v_toBind_960_,
        lean_box(0),
        lean_box(0),
        v___x_963_,
        v___f_962_,
    );
    return v___x_964_;
}
pub unsafe fn l_List_mapMonoM___redArg(
    mut v_inst_965_: *mut LeanObject,
    mut v_as_966_: *mut LeanObject,
    mut v_f_967_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_as_966_) == 0 {
        let mut v_toApplicative_968_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_968_ = lean_ctor_get(v_inst_965_, 0);
        lean_inc_ref(v_toApplicative_968_);
        lean_dec(v_f_967_);
        lean_dec_ref(v_inst_965_);
        v_toPure_969_ = lean_ctor_get(v_toApplicative_968_, 1);
        lean_inc(v_toPure_969_);
        lean_dec_ref(v_toApplicative_968_);
        v___x_970_ = lean_apply_2(v_toPure_969_, lean_box(0), v_as_966_);
        return v___x_970_;
    } else {
        let mut v_toApplicative_971_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_972_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_973_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_974_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_971_ = lean_ctor_get(v_inst_965_, 0);
        v_toBind_972_ = lean_ctor_get(v_inst_965_, 1);
        lean_inc_n(v_toBind_972_, 2);
        v_toPure_973_ = lean_ctor_get(v_toApplicative_971_, 1);
        lean_inc(v_toPure_973_);
        v_head_974_ = lean_ctor_get(v_as_966_, 0);
        lean_inc(v_head_974_);
        v_tail_975_ = lean_ctor_get(v_as_966_, 1);
        lean_inc(v_tail_975_);
        lean_dec_ref_known(v_as_966_, 2);
        lean_inc(v_f_967_);
        v___f_976_ = lean_alloc_closure(
            l_List_mapMonoM___redArg___lam__1 as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_976_, 0, v_toPure_973_);
        lean_closure_set(v___f_976_, 1, v_inst_965_);
        lean_closure_set(v___f_976_, 2, v_tail_975_);
        lean_closure_set(v___f_976_, 3, v_f_967_);
        lean_closure_set(v___f_976_, 4, v_toBind_972_);
        v___x_977_ = lean_apply_1(v_f_967_, v_head_974_);
        v___x_978_ = lean_apply_4(
            v_toBind_972_,
            lean_box(0),
            lean_box(0),
            v___x_977_,
            v___f_976_,
        );
        return v___x_978_;
    }
}
pub unsafe fn l_List_mapMonoM(
    mut v_m_979_: *mut LeanObject,
    mut v_00_u03b1_980_: *mut LeanObject,
    mut v_inst_981_: *mut LeanObject,
    mut v_as_982_: *mut LeanObject,
    mut v_f_983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    v___x_984_ = l_List_mapMonoM___redArg(v_inst_981_, v_as_982_, v_f_983_);
    return v___x_984_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(
    mut v_f_985_: *mut LeanObject,
    mut v_as_986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_992_: u8 = 0;
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_999_: u8 = 0;
    let mut v_unused_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: usize = 0;
    let mut v___x_1003_: usize = 0;
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: usize = 0;
    let mut v___x_1007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_986_) == 0 {
                    lean_dec(v_f_985_);
                    return v_as_986_;
                } else {
                    v_head_987_ = lean_ctor_get(v_as_986_, 0);
                    v_tail_988_ = lean_ctor_get(v_as_986_, 1);
                    lean_inc(v_f_985_);
                    lean_inc(v_head_987_);
                    v___x_989_ = lean_apply_1(v_f_985_, v_head_987_);
                    lean_inc(v_tail_988_);
                    v___x_990_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(v_f_985_, v_tail_988_);
                    v___x_1002_ = lean_ptr_addr(v___x_989_);
                    v___x_1003_ = lean_ptr_addr(v_head_987_);
                    v___x_1004_ = lean_usize_dec_eq(v___x_1002_, v___x_1003_);
                    if v___x_1004_ == 0 {
                        v___y_992_ = v___x_1004_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1005_ = lean_ptr_addr(v___x_990_);
                        v___x_1006_ = lean_ptr_addr(v_tail_988_);
                        v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
                        v___y_992_ = v___x_1007_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_992_ == 0 {
                    v_isSharedCheck_999_ = (!lean_is_exclusive(v_as_986_)) as u8;
                    if v_isSharedCheck_999_ == 0 {
                        v_unused_1000_ = lean_ctor_get(v_as_986_, 1);
                        lean_dec(v_unused_1000_);
                        v_unused_1001_ = lean_ctor_get(v_as_986_, 0);
                        lean_dec(v_unused_1001_);
                        v___x_994_ = v_as_986_;
                        v_isShared_995_ = v_isSharedCheck_999_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_as_986_);
                        v___x_994_ = lean_box(0);
                        v_isShared_995_ = v_isSharedCheck_999_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_990_);
                    lean_dec(v___x_989_);
                    return v_as_986_;
                }
            }
            2 => {
                if v_isShared_995_ == 0 {
                    lean_ctor_set(v___x_994_, 1, v___x_990_);
                    lean_ctor_set(v___x_994_, 0, v___x_989_);
                    v___x_997_ = v___x_994_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_989_);
                    lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_990_);
                    v___x_997_ = v_reuseFailAlloc_998_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapMono___redArg(
    mut v_as_1008_: *mut LeanObject,
    mut v_f_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1010_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(v_f_1009_, v_as_1008_);
    return v___x_1010_;
}
pub unsafe fn l_List_mapMono(
    mut v_00_u03b1_1011_: *mut LeanObject,
    mut v_as_1012_: *mut LeanObject,
    mut v_f_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    v___x_1014_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(v_f_1013_, v_as_1012_);
    return v___x_1014_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0(
    mut v_00_u03b1_1015_: *mut LeanObject,
    mut v_f_1016_: *mut LeanObject,
    mut v_as_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    v___x_1018_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(v_f_1016_, v_as_1017_);
    return v___x_1018_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20()
-> *mut LeanObject {
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    v___x_1075_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19;
    v___x_1076_ = l_String_toRawSubstring_x27(v___x_1075_);
    return v___x_1076_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34()
-> *mut LeanObject {
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    v___x_1109_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__33;
    v___x_1110_ = l_String_toRawSubstring_x27(v___x_1109_);
    return v___x_1110_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48()
-> *mut LeanObject {
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    v___x_1139_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__47;
    v___x_1140_ = l_String_toRawSubstring_x27(v___x_1139_);
    return v___x_1140_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56()
-> *mut LeanObject {
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    v___x_1156_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55;
    v___x_1157_ = l_String_toRawSubstring_x27(v___x_1156_);
    return v___x_1157_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59()
-> *mut LeanObject {
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Array_mkArray0(lean_box(0));
    return v___x_1161_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77()
-> *mut LeanObject {
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    v___x_1205_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76;
    v___x_1206_ = l_String_toRawSubstring_x27(v___x_1205_);
    return v___x_1206_;
}
pub unsafe fn l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1(
    mut v_x_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
    mut v_a_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: u8 = 0;
    v___x_1212_ = l_List_tacticSizeOf__list__dec___closed__2;
    v___x_1213_ = l_Lean_Syntax_isOfKind(v_x_1209_, v___x_1212_);
    if v___x_1213_ == 0 {
        let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
        v___x_1214_ = lean_box(1);
        v___x_1215_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1215_, 0, v___x_1214_);
        lean_ctor_set(v___x_1215_, 1, v_a_1211_);
        return v___x_1215_;
    } else {
        let mut v_quotContext_1216_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1217_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1219_: u8 = 0;
        let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1216_ = lean_ctor_get(v_a_1210_, 1);
        v_currMacroScope_1217_ = lean_ctor_get(v_a_1210_, 2);
        v_ref_1218_ = lean_ctor_get(v_a_1210_, 5);
        v___x_1219_ = 0;
        v___x_1220_ = l_Lean_SourceInfo_fromRef(v_ref_1218_, v___x_1219_);
        v___x_1221_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3;
        v___x_1222_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4;
        lean_inc_n(v___x_1220_, 61);
        v___x_1223_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1223_, 0, v___x_1220_);
        lean_ctor_set(v___x_1223_, 1, v___x_1221_);
        v___x_1224_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__6;
        v___x_1225_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__8;
        v___x_1226_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__9;
        v___x_1227_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1227_, 0, v___x_1220_);
        lean_ctor_set(v___x_1227_, 1, v___x_1226_);
        v___x_1228_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11;
        v___x_1229_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13;
        v___x_1230_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15;
        v___x_1231_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__16;
        v___x_1232_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1232_, 0, v___x_1220_);
        lean_ctor_set(v___x_1232_, 1, v___x_1231_);
        v___x_1233_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17;
        v___x_1234_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18;
        v___x_1235_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1235_, 0, v___x_1220_);
        lean_ctor_set(v___x_1235_, 1, v___x_1233_);
        v___x_1236_ = lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20_once), _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20);
        v___x_1237_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__21;
        lean_inc_n(v_currMacroScope_1217_, 5);
        lean_inc_n(v_quotContext_1216_, 5);
        v___x_1238_ =
            l_Lean_addMacroScope(v_quotContext_1216_, v___x_1237_, v_currMacroScope_1217_);
        v___x_1239_ = lean_box(0);
        v___x_1240_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__24;
        v___x_1241_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1241_, 0, v___x_1220_);
        lean_ctor_set(v___x_1241_, 1, v___x_1236_);
        lean_ctor_set(v___x_1241_, 2, v___x_1238_);
        lean_ctor_set(v___x_1241_, 3, v___x_1240_);
        lean_inc_ref(v___x_1241_);
        lean_inc_ref(v___x_1235_);
        v___x_1242_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1234_, v___x_1235_, v___x_1241_);
        v___x_1243_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__25;
        v___x_1244_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1244_, 0, v___x_1220_);
        lean_ctor_set(v___x_1244_, 1, v___x_1243_);
        v___x_1245_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26;
        v___x_1246_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27;
        v___x_1247_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1247_, 0, v___x_1220_);
        lean_ctor_set(v___x_1247_, 1, v___x_1245_);
        v___x_1248_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1246_, v___x_1247_);
        v___x_1249_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28;
        v___x_1250_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29;
        v___x_1251_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1251_, 0, v___x_1220_);
        lean_ctor_set(v___x_1251_, 1, v___x_1249_);
        v___x_1252_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1250_, v___x_1251_);
        lean_inc(v___x_1248_);
        lean_inc_ref(v___x_1244_);
        v___x_1253_ = l_Lean_Syntax_node5(
            v___x_1220_,
            v___x_1224_,
            v___x_1242_,
            v___x_1244_,
            v___x_1248_,
            v___x_1244_,
            v___x_1252_,
        );
        v___x_1254_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1229_, v___x_1253_);
        v___x_1255_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1228_, v___x_1254_);
        lean_inc_ref(v___x_1232_);
        v___x_1256_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1230_, v___x_1232_, v___x_1255_);
        v___x_1257_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1224_, v___x_1256_);
        v___x_1258_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1229_, v___x_1257_);
        v___x_1259_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1228_, v___x_1258_);
        lean_inc_ref(v___x_1227_);
        v___x_1260_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1225_, v___x_1227_, v___x_1259_);
        v___x_1261_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32;
        v___x_1262_ = lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34_once), _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34);
        v___x_1263_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37;
        v___x_1264_ =
            l_Lean_addMacroScope(v_quotContext_1216_, v___x_1263_, v_currMacroScope_1217_);
        v___x_1265_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__39;
        v___x_1266_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1266_, 0, v___x_1220_);
        lean_ctor_set(v___x_1266_, 1, v___x_1262_);
        lean_ctor_set(v___x_1266_, 2, v___x_1264_);
        lean_ctor_set(v___x_1266_, 3, v___x_1265_);
        v___x_1267_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41;
        v___x_1268_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43;
        v___x_1269_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__44;
        v___x_1270_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1270_, 0, v___x_1220_);
        lean_ctor_set(v___x_1270_, 1, v___x_1269_);
        v___x_1271_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__46;
        v___x_1272_ = lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48_once), _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48);
        v___x_1273_ = lean_box(0);
        v___x_1274_ =
            l_Lean_addMacroScope(v_quotContext_1216_, v___x_1273_, v_currMacroScope_1217_);
        v___x_1275_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__51;
        v___x_1276_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1276_, 0, v___x_1220_);
        lean_ctor_set(v___x_1276_, 1, v___x_1272_);
        lean_ctor_set(v___x_1276_, 2, v___x_1274_);
        lean_ctor_set(v___x_1276_, 3, v___x_1275_);
        v___x_1277_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1271_, v___x_1276_);
        v___x_1278_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1268_, v___x_1270_, v___x_1277_);
        v___x_1279_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53;
        v___x_1280_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__54;
        v___x_1281_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1281_, 0, v___x_1220_);
        lean_ctor_set(v___x_1281_, 1, v___x_1280_);
        v___x_1282_ = lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56_once), _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56);
        v___x_1283_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__57;
        v___x_1284_ =
            l_Lean_addMacroScope(v_quotContext_1216_, v___x_1283_, v_currMacroScope_1217_);
        v___x_1285_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1285_, 0, v___x_1220_);
        lean_ctor_set(v___x_1285_, 1, v___x_1282_);
        lean_ctor_set(v___x_1285_, 2, v___x_1284_);
        lean_ctor_set(v___x_1285_, 3, v___x_1239_);
        lean_inc_ref(v___x_1285_);
        v___x_1286_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1279_, v___x_1281_, v___x_1285_);
        v___x_1287_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1224_, v___x_1286_);
        v___x_1288_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1261_, v___x_1241_, v___x_1287_);
        v___x_1289_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__58;
        v___x_1290_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1290_, 0, v___x_1220_);
        lean_ctor_set(v___x_1290_, 1, v___x_1289_);
        v___x_1291_ = l_Lean_Syntax_node3(
            v___x_1220_,
            v___x_1267_,
            v___x_1278_,
            v___x_1288_,
            v___x_1290_,
        );
        v___x_1292_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1224_, v___x_1291_);
        v___x_1293_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1261_, v___x_1266_, v___x_1292_);
        v___x_1294_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1234_, v___x_1235_, v___x_1293_);
        v___x_1295_ = lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59_once), _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59);
        v___x_1296_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1296_, 0, v___x_1220_);
        lean_ctor_set(v___x_1296_, 1, v___x_1224_);
        lean_ctor_set(v___x_1296_, 2, v___x_1295_);
        v___x_1297_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60;
        v___x_1298_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61;
        v___x_1299_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1299_, 0, v___x_1220_);
        lean_ctor_set(v___x_1299_, 1, v___x_1297_);
        v___x_1300_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63;
        v___x_1301_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65;
        v___x_1302_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1301_, v___x_1285_);
        lean_inc_ref_n(v___x_1296_, 6);
        v___x_1303_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1300_, v___x_1302_, v___x_1296_);
        v___x_1304_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1224_, v___x_1303_);
        v___x_1305_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__66;
        v___x_1306_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1306_, 0, v___x_1220_);
        lean_ctor_set(v___x_1306_, 1, v___x_1305_);
        v___x_1307_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1224_, v___x_1248_);
        v___x_1308_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1229_, v___x_1307_);
        v___x_1309_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1228_, v___x_1308_);
        v___x_1310_ = l_Lean_Syntax_node4(
            v___x_1220_,
            v___x_1298_,
            v___x_1299_,
            v___x_1304_,
            v___x_1306_,
            v___x_1309_,
        );
        v___x_1311_ = l_Lean_Syntax_node3(
            v___x_1220_,
            v___x_1224_,
            v___x_1294_,
            v___x_1296_,
            v___x_1310_,
        );
        v___x_1312_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1229_, v___x_1311_);
        v___x_1313_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1228_, v___x_1312_);
        v___x_1314_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1230_, v___x_1232_, v___x_1313_);
        v___x_1315_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67;
        v___x_1316_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68;
        v___x_1317_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1317_, 0, v___x_1220_);
        lean_ctor_set(v___x_1317_, 1, v___x_1315_);
        v___x_1318_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70;
        v___x_1319_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72;
        v___x_1320_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74;
        v___x_1321_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__75;
        v___x_1322_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1322_, 0, v___x_1220_);
        lean_ctor_set(v___x_1322_, 1, v___x_1321_);
        v___x_1323_ = lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77_once), _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77);
        v___x_1324_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__78;
        v___x_1325_ =
            l_Lean_addMacroScope(v_quotContext_1216_, v___x_1324_, v_currMacroScope_1217_);
        v___x_1326_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1326_, 0, v___x_1220_);
        lean_ctor_set(v___x_1326_, 1, v___x_1323_);
        lean_ctor_set(v___x_1326_, 2, v___x_1325_);
        lean_ctor_set(v___x_1326_, 3, v___x_1239_);
        v___x_1327_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1320_, v___x_1322_, v___x_1326_);
        v___x_1328_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1319_, v___x_1327_);
        v___x_1329_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1224_, v___x_1328_);
        v___x_1330_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1318_, v___x_1329_);
        v___x_1331_ = l_Lean_Syntax_node6(
            v___x_1220_,
            v___x_1316_,
            v___x_1317_,
            v___x_1330_,
            v___x_1296_,
            v___x_1296_,
            v___x_1296_,
            v___x_1296_,
        );
        v___x_1332_ = l_Lean_Syntax_node3(
            v___x_1220_,
            v___x_1224_,
            v___x_1314_,
            v___x_1296_,
            v___x_1331_,
        );
        v___x_1333_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1229_, v___x_1332_);
        v___x_1334_ = l_Lean_Syntax_node1(v___x_1220_, v___x_1228_, v___x_1333_);
        v___x_1335_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1225_, v___x_1227_, v___x_1334_);
        v___x_1336_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1224_, v___x_1260_, v___x_1335_);
        v___x_1337_ = l_Lean_Syntax_node2(v___x_1220_, v___x_1222_, v___x_1223_, v___x_1336_);
        v___x_1338_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1338_, 0, v___x_1337_);
        lean_ctor_set(v___x_1338_, 1, v_a_1211_);
        return v___x_1338_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___boxed(
    mut v_x_1339_: *mut LeanObject,
    mut v_a_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1342_: *mut LeanObject = core::ptr::null_mut();
    v_res_1342_ =
        l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1(
            v_x_1339_, v_a_1340_, v_a_1341_,
        );
    lean_dec_ref(v_a_1340_);
    return v_res_1342_;
}
pub unsafe fn l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1(
    mut v_x_1346_: *mut LeanObject,
    mut v_a_1347_: *mut LeanObject,
    mut v_a_1348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: u8 = 0;
    v___x_1349_ = l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1350_ = l_Lean_Syntax_isOfKind(v_x_1346_, v___x_1349_);
    if v___x_1350_ == 0 {
        let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
        v___x_1351_ = lean_box(1);
        v___x_1352_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1352_, 0, v___x_1351_);
        lean_ctor_set(v___x_1352_, 1, v_a_1348_);
        return v___x_1352_;
    } else {
        let mut v_ref_1353_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1354_: u8 = 0;
        let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
        v_ref_1353_ = lean_ctor_get(v_a_1347_, 5);
        v___x_1354_ = 0;
        v___x_1355_ = l_Lean_SourceInfo_fromRef(v_ref_1353_, v___x_1354_);
        v___x_1356_ = l_List_tacticSizeOf__list__dec___closed__2;
        v___x_1357_ = l_List_tacticSizeOf__list__dec___closed__3;
        lean_inc(v___x_1355_);
        v___x_1358_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1358_, 0, v___x_1355_);
        lean_ctor_set(v___x_1358_, 1, v___x_1357_);
        v___x_1359_ = l_Lean_Syntax_node1(v___x_1355_, v___x_1356_, v___x_1358_);
        v___x_1360_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1360_, 0, v___x_1359_);
        lean_ctor_set(v___x_1360_, 1, v_a_1348_);
        return v___x_1360_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___boxed(
    mut v_x_1361_: *mut LeanObject,
    mut v_a_1362_: *mut LeanObject,
    mut v_a_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1364_: *mut LeanObject = core::ptr::null_mut();
    v_res_1364_ =
        l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1(
            v_x_1361_, v_a_1362_, v_a_1363_,
        );
    lean_dec_ref(v_a_1362_);
    return v_res_1364_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___redArg(
    mut v_x_1365_: *mut LeanObject,
    mut v_x_1366_: *mut LeanObject,
    mut v_h__1_1367_: *mut LeanObject,
    mut v_h__2_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1372_: u8 = 0;
    v_head_1369_ = lean_ctor_get(v_x_1365_, 0);
    lean_inc(v_head_1369_);
    v_tail_1370_ = lean_ctor_get(v_x_1365_, 1);
    lean_inc(v_tail_1370_);
    lean_dec(v_x_1365_);
    v_zero_1371_ = lean_unsigned_to_nat(0);
    v_isZero_1372_ = lean_nat_dec_eq(v_x_1366_, v_zero_1371_);
    if v_isZero_1372_ == 1 {
        let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1368_);
        v___x_1373_ = lean_apply_3(v_h__1_1367_, v_head_1369_, v_tail_1370_, lean_box(0));
        return v___x_1373_;
    } else {
        let mut v_one_1374_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1367_);
        v_one_1374_ = lean_unsigned_to_nat(1);
        v_n_1375_ = lean_nat_sub(v_x_1366_, v_one_1374_);
        v___x_1376_ = lean_apply_4(
            v_h__2_1368_,
            v_head_1369_,
            v_tail_1370_,
            v_n_1375_,
            lean_box(0),
        );
        return v___x_1376_;
    }
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___redArg___boxed(
    mut v_x_1377_: *mut LeanObject,
    mut v_x_1378_: *mut LeanObject,
    mut v_h__1_1379_: *mut LeanObject,
    mut v_h__2_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1381_: *mut LeanObject = core::ptr::null_mut();
    v_res_1381_ = l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___redArg(
        v_x_1377_,
        v_x_1378_,
        v_h__1_1379_,
        v_h__2_1380_,
    );
    lean_dec(v_x_1378_);
    return v_res_1381_;
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter(
    mut v_00_u03b1_1382_: *mut LeanObject,
    mut v_motive_1383_: *mut LeanObject,
    mut v_x_1384_: *mut LeanObject,
    mut v_x_1385_: *mut LeanObject,
    mut v_h__1_1386_: *mut LeanObject,
    mut v_h__2_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1391_: u8 = 0;
    v_head_1388_ = lean_ctor_get(v_x_1384_, 0);
    lean_inc(v_head_1388_);
    v_tail_1389_ = lean_ctor_get(v_x_1384_, 1);
    lean_inc(v_tail_1389_);
    lean_dec(v_x_1384_);
    v_zero_1390_ = lean_unsigned_to_nat(0);
    v_isZero_1391_ = lean_nat_dec_eq(v_x_1385_, v_zero_1390_);
    if v_isZero_1391_ == 1 {
        let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1387_);
        v___x_1392_ = lean_apply_3(v_h__1_1386_, v_head_1388_, v_tail_1389_, lean_box(0));
        return v___x_1392_;
    } else {
        let mut v_one_1393_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1386_);
        v_one_1393_ = lean_unsigned_to_nat(1);
        v_n_1394_ = lean_nat_sub(v_x_1385_, v_one_1393_);
        v___x_1395_ = lean_apply_4(
            v_h__2_1387_,
            v_head_1388_,
            v_tail_1389_,
            v_n_1394_,
            lean_box(0),
        );
        return v___x_1395_;
    }
}
pub unsafe fn l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___boxed(
    mut v_00_u03b1_1396_: *mut LeanObject,
    mut v_motive_1397_: *mut LeanObject,
    mut v_x_1398_: *mut LeanObject,
    mut v_x_1399_: *mut LeanObject,
    mut v_h__1_1400_: *mut LeanObject,
    mut v_h__2_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1402_: *mut LeanObject = core::ptr::null_mut();
    v_res_1402_ = l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter(
        v_00_u03b1_1396_,
        v_motive_1397_,
        v_x_1398_,
        v_x_1399_,
        v_h__1_1400_,
        v_h__2_1401_,
    );
    lean_dec(v_x_1399_);
    return v_res_1402_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_BasicAux(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_BasicAux(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_BasicAux(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_BasicAux(builtin);
}
