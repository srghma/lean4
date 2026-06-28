// Lean compiler output
// Module: Init.LawfulBEqTactics
// Imports: Init.Core Init.Data.Bool Init.ByCases Init.Classical
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value: LeanStringObject<
    16,
> = LeanStringObject {
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
        68, 101, 114, 105, 118, 105, 110, 103, 72, 101, 108, 112, 101, 114, 115, 0,
    ],
};
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value)
        as *mut LeanObject;
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1_value: LeanStringObject<
    29,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        116, 97, 99, 116, 105, 99, 68, 101, 114, 105, 118, 105, 110, 103, 95, 82, 101, 102, 108,
        69, 113, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1_value)
        as *mut LeanObject;
static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value)
                as *mut LeanObject,
            15296920709769342228 as *mut LeanObject,
        ],
    };
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1_value)
                as *mut LeanObject,
            8670410953647023675 as *mut LeanObject,
        ],
    };
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value)
        as *mut LeanObject;
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3_value: LeanStringObject<
    23,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        100, 101, 114, 105, 118, 105, 110, 103, 95, 82, 101, 102, 108, 69, 113, 95, 116, 97, 99,
        116, 105, 99, 0,
    ],
};
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3_value)
        as *mut LeanObject;
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4_value)
        as *mut LeanObject;
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5_value)
        as *mut LeanObject;
pub static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic: *mut LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5_value)
        as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value) as *mut LeanObject,8689124066155232629 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 116, 114, 111, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12_value) as *mut LeanObject,5665407707378192681 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14_value) as *mut LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14_value) as *mut LeanObject,13655884332201764339 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16_value) as *mut LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18_value) as *mut LeanObject,1203031414467445991 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 105, 109, 84, 97, 114, 103, 101, 116, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20_value) as *mut LeanObject,12379583263280086920 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 108, 108, 71, 111, 97, 108, 115, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22_value) as *mut LeanObject,14131640301685195369 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25_value) as *mut LeanObject,12783917532758215986 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27_value) as *mut LeanObject,3488656302031949961 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 110, 108, 121, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31_value) as *mut LeanObject,7383208167966365478 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 69, 113, 46, 114, 101, 102, 108, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33_value) as *mut LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34: *mut LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 101, 102, 108, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35_value) as *mut LeanObject,16093780639914376387 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36_value) as *mut LeanObject,2931058100974671924 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 105, 109, 112, 80, 114, 101, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41_value) as *mut LeanObject,10994783280459430853 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 147, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 100, 117, 99, 101, 68, 73, 116, 101, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44_value) as *mut LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45: *mut LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44_value) as *mut LeanObject,5427593982451803422 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [66, 111, 111, 108, 46, 97, 110, 100, 95, 116, 114, 117, 101, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47_value) as *mut LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48: *mut LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 110, 100, 95, 116, 114, 117, 101, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50_value) as *mut LeanObject,4834393437129725208 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 83, 116, 97, 114, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54_value) as *mut LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54_value) as *mut LeanObject,2669418402702632573 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 66, 69, 113, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57_value) as *mut LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58: *mut LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57_value) as *mut LeanObject,7878093518326082311 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 73, 100, 120, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60_value) as *mut LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61: *mut LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60_value) as *mut LeanObject,11681431521506135087 as *mut LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63_value) as *mut LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64: *mut LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64_value) as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__0_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            116, 97, 99, 116, 105, 99, 68, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102,
            117, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 95, 115, 116, 101, 112, 0,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__0_value)
        as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__0_value)
                as *mut LeanObject,
            5824473086672787675 as *mut LeanObject,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__1_value)
        as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__2_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            100, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102, 117, 108, 69, 113, 95,
            116, 97, 99, 116, 105, 99, 95, 115, 116, 101, 112, 0,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__2_value)
        as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__3_value)
        as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__4_value)
        as *mut LeanObject;
pub static mut l_tacticDeriving__LawfulEq__tactic__step: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__4_value)
        as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [102, 97, 105, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0_value) as *mut LeanObject,59994724629665531 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2_value) as *mut LeanObject,9232979286016572671 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [34, 100, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102, 117, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 95, 115, 116, 101, 112, 32, 102, 97, 105, 108, 101, 100, 34, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0_value) as *mut LeanObject,6022092293134036165 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 97, 110, 103, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3_value) as *mut LeanObject,16580879115603664356 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 114, 111, 119, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6_value) as *mut LeanObject,14917456309791986358 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 61, 95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8_value) as *mut LeanObject,5677895497334651815 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12_value) as *mut LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12_value) as *mut LeanObject,8391571994004792969 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22_value) as *mut LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 61, 61, 95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26_value) as *mut LeanObject,1990087968466729753 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28_value) as *mut LeanObject,3984140175429830279 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 61, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [61, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value) as *mut LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value) as *mut LeanObject,6560861498103128555 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value) as *mut LeanObject,9255189395584251158 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 146, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 102, 105, 110, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40_value) as *mut LeanObject,17704266427038597681 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42_value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 72, 101, 108, 112, 101, 114, 115, 46, 100, 101, 114, 105, 118, 105, 110, 103, 95, 108, 97, 119, 102, 117, 108, 95, 98, 101, 113, 95, 104, 101, 108, 112, 101, 114, 95, 100, 101, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42_value) as *mut LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [100, 101, 114, 105, 118, 105, 110, 103, 95, 108, 97, 119, 102, 117, 108, 95, 98, 101, 113, 95, 104, 101, 108, 112, 101, 114, 95, 100, 101, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value) as *mut LeanObject,15296920709769342228 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44_value) as *mut LeanObject,8566119949188782736 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48_value) as *mut LeanObject,11921244625177918938 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 100, 111, 116, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51_value) as *mut LeanObject,17509453262750390254 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 100, 111, 116, 84, 107, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53_value) as *mut LeanObject,10467776374279798389 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 1, m_data: [194, 183, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 111, 108, 118, 101, 84, 97, 99, 116, 105, 99, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56_value) as *mut LeanObject,17642938439725768139 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 108, 118, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59_value) as *mut LeanObject,2214559063752339918 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [97, 112, 112, 108, 121, 65, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62_value) as *mut LeanObject,6767535199982504454 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [97, 112, 112, 108, 121, 95, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [34, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 105, 115, 99, 104, 97, 114, 103, 101, 32, 101, 113, 95, 111, 102, 95, 98, 101, 113, 32, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 34, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66_value) as *mut LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66_value) as *mut LeanObject,8738205681931236784 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 115, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69_value) as *mut LeanObject,5378309054007488965 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 115, 105, 109, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71_value) as *mut LeanObject,5511199417188169206 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 72, 101, 108, 112, 101, 114, 115, 46, 100, 101, 114, 105, 118, 105, 110, 103, 95, 108, 97, 119, 102, 117, 108, 95, 98, 101, 113, 95, 104, 101, 108, 112, 101, 114, 95, 110, 100, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3_value) as *mut LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [100, 101, 114, 105, 118, 105, 110, 103, 95, 108, 97, 119, 102, 117, 108, 95, 98, 101, 113, 95, 104, 101, 108, 112, 101, 114, 95, 110, 100, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value) as *mut LeanObject,15296920709769342228 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5_value) as *mut LeanObject,14609763185561287494 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 117, 98, 115, 116, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9_value) as *mut LeanObject,10450510229121596744 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 38, 38, 95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0_value) as *mut LeanObject,1601449343645893382 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [38, 38, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 72, 101, 108, 112, 101, 114, 115, 46, 97, 110, 100, 95, 116, 114, 117, 101, 95, 99, 117, 114, 114, 121, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3_value) as *mut LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 110, 100, 95, 116, 114, 117, 101, 95, 99, 117, 114, 114, 121, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value) as *mut LeanObject,15296920709769342228 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5_value) as *mut LeanObject,17404699193326600018 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0_value) as *mut LeanObject,3294379458557754569 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 102, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 113, 49, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0_value) as *mut LeanObject,8471002125274025202 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 99, 116, 105, 99, 84, 114, 105, 118, 105, 97, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3_value) as *mut LeanObject,2766452847008772443 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 105, 118, 105, 97, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5_value) as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__0_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            116, 97, 99, 116, 105, 99, 68, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102,
            117, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__0_value) as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__0_value)
                as *mut LeanObject,
            12369115935240678623 as *mut LeanObject,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__1_value) as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__2_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            100, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102, 117, 108, 69, 113, 95,
            116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__2_value) as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__3_value) as *mut LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__4_value) as *mut LeanObject;
pub static mut l_tacticDeriving__LawfulEq__tactic: *mut LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [121, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0_value) as *mut LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0_value) as *mut LeanObject,10873459229016405832 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 99, 116, 105, 99, 82, 101, 112, 101, 97, 116, 95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3_value) as *mut LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3_value) as *mut LeanObject,16592576665728214421 as *mut LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value) as *mut LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 112, 101, 97, 116, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5_value) as *mut LeanObject;
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15()
-> *mut LeanObject {
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14;
    v___x_1217_ = l_String_toRawSubstring_x27(v___x_1216_);
    return v___x_1217_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17()
-> *mut LeanObject {
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    v___x_1220_ = l_Array_mkArray0(lean_box(0));
    return v___x_1220_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34()
-> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33;
    v___x_1262_ = l_String_toRawSubstring_x27(v___x_1261_);
    return v___x_1262_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45()
-> *mut LeanObject {
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    v___x_1283_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44;
    v___x_1284_ = l_String_toRawSubstring_x27(v___x_1283_);
    return v___x_1284_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48()
-> *mut LeanObject {
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1288_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47;
    v___x_1289_ = l_String_toRawSubstring_x27(v___x_1288_);
    return v___x_1289_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58()
-> *mut LeanObject {
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    v___x_1309_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57;
    v___x_1310_ = l_String_toRawSubstring_x27(v___x_1309_);
    return v___x_1310_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61()
-> *mut LeanObject {
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60;
    v___x_1315_ = l_String_toRawSubstring_x27(v___x_1314_);
    return v___x_1315_;
}
pub unsafe fn l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1(
    mut v_x_1320_: *mut LeanObject,
    mut v_a_1321_: *mut LeanObject,
    mut v_a_1322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: u8 = 0;
    v___x_1323_ = l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2;
    v___x_1324_ = l_Lean_Syntax_isOfKind(v_x_1320_, v___x_1323_);
    if v___x_1324_ == 0 {
        let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
        v___x_1325_ = lean_box(1);
        v___x_1326_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1326_, 0, v___x_1325_);
        lean_ctor_set(v___x_1326_, 1, v_a_1322_);
        return v___x_1326_;
    } else {
        let mut v_quotContext_1327_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1328_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: u8 = 0;
        let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1327_ = lean_ctor_get(v_a_1321_, 1);
        v_currMacroScope_1328_ = lean_ctor_get(v_a_1321_, 2);
        v_ref_1329_ = lean_ctor_get(v_a_1321_, 5);
        v___x_1330_ = 0;
        v___x_1331_ = l_Lean_SourceInfo_fromRef(v_ref_1329_, v___x_1330_);
        v___x_1332_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_1333_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        lean_inc_n(v___x_1331_, 44);
        v___x_1334_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1334_, 0, v___x_1331_);
        lean_ctor_set(v___x_1334_, 1, v___x_1333_);
        v___x_1335_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_1336_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_1337_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_1338_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_1339_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        v___x_1340_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1340_, 0, v___x_1331_);
        lean_ctor_set(v___x_1340_, 1, v___x_1338_);
        v___x_1341_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15);
        v___x_1342_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16;
        lean_inc_n(v_currMacroScope_1328_, 6);
        lean_inc_n(v_quotContext_1327_, 6);
        v___x_1343_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1342_, v_currMacroScope_1328_);
        v___x_1344_ = lean_box(0);
        v___x_1345_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1345_, 0, v___x_1331_);
        lean_ctor_set(v___x_1345_, 1, v___x_1341_);
        lean_ctor_set(v___x_1345_, 2, v___x_1343_);
        lean_ctor_set(v___x_1345_, 3, v___x_1344_);
        lean_inc_ref(v___x_1345_);
        v___x_1346_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1345_);
        v___x_1347_ = l_Lean_Syntax_node2(v___x_1331_, v___x_1339_, v___x_1340_, v___x_1346_);
        v___x_1348_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_1349_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1349_, 0, v___x_1331_);
        lean_ctor_set(v___x_1349_, 1, v___x_1337_);
        lean_ctor_set(v___x_1349_, 2, v___x_1348_);
        v___x_1350_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18;
        v___x_1351_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19;
        v___x_1352_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1352_, 0, v___x_1331_);
        lean_ctor_set(v___x_1352_, 1, v___x_1350_);
        v___x_1353_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21;
        lean_inc_ref_n(v___x_1349_, 17);
        v___x_1354_ = l_Lean_Syntax_node2(v___x_1331_, v___x_1353_, v___x_1349_, v___x_1345_);
        v___x_1355_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1354_);
        v___x_1356_ = l_Lean_Syntax_node5(
            v___x_1331_,
            v___x_1351_,
            v___x_1352_,
            v___x_1355_,
            v___x_1349_,
            v___x_1349_,
            v___x_1349_,
        );
        v___x_1357_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23;
        v___x_1358_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24;
        v___x_1359_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1359_, 0, v___x_1331_);
        lean_ctor_set(v___x_1359_, 1, v___x_1358_);
        v___x_1360_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25;
        v___x_1361_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26;
        v___x_1362_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1362_, 0, v___x_1331_);
        lean_ctor_set(v___x_1362_, 1, v___x_1360_);
        v___x_1363_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28;
        v___x_1364_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1363_, v___x_1349_);
        v___x_1365_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29;
        v___x_1366_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1366_, 0, v___x_1331_);
        lean_ctor_set(v___x_1366_, 1, v___x_1365_);
        v___x_1367_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1366_);
        v___x_1368_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30;
        v___x_1369_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1369_, 0, v___x_1331_);
        lean_ctor_set(v___x_1369_, 1, v___x_1368_);
        v___x_1370_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32;
        v___x_1371_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34);
        v___x_1372_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37;
        v___x_1373_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1372_, v_currMacroScope_1328_);
        v___x_1374_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39;
        v___x_1375_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1375_, 0, v___x_1331_);
        lean_ctor_set(v___x_1375_, 1, v___x_1371_);
        lean_ctor_set(v___x_1375_, 2, v___x_1373_);
        lean_ctor_set(v___x_1375_, 3, v___x_1374_);
        v___x_1376_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1349_,
            v___x_1349_,
            v___x_1375_,
        );
        v___x_1377_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40;
        v___x_1378_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1378_, 0, v___x_1331_);
        lean_ctor_set(v___x_1378_, 1, v___x_1377_);
        v___x_1379_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42;
        v___x_1380_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43;
        v___x_1381_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1381_, 0, v___x_1331_);
        lean_ctor_set(v___x_1381_, 1, v___x_1380_);
        v___x_1382_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1379_, v___x_1381_);
        v___x_1383_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1382_);
        v___x_1384_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45);
        v___x_1385_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46;
        v___x_1386_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1385_, v_currMacroScope_1328_);
        v___x_1387_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1387_, 0, v___x_1331_);
        lean_ctor_set(v___x_1387_, 1, v___x_1384_);
        lean_ctor_set(v___x_1387_, 2, v___x_1386_);
        lean_ctor_set(v___x_1387_, 3, v___x_1344_);
        v___x_1388_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1383_,
            v___x_1349_,
            v___x_1387_,
        );
        v___x_1389_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48);
        v___x_1390_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51;
        v___x_1391_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1390_, v_currMacroScope_1328_);
        v___x_1392_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53;
        v___x_1393_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1393_, 0, v___x_1331_);
        lean_ctor_set(v___x_1393_, 1, v___x_1389_);
        lean_ctor_set(v___x_1393_, 2, v___x_1391_);
        lean_ctor_set(v___x_1393_, 3, v___x_1392_);
        v___x_1394_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1349_,
            v___x_1349_,
            v___x_1393_,
        );
        v___x_1395_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55;
        v___x_1396_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56;
        v___x_1397_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1397_, 0, v___x_1331_);
        lean_ctor_set(v___x_1397_, 1, v___x_1396_);
        v___x_1398_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1395_, v___x_1397_);
        v___x_1399_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58);
        v___x_1400_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59;
        v___x_1401_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1400_, v_currMacroScope_1328_);
        v___x_1402_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1402_, 0, v___x_1331_);
        lean_ctor_set(v___x_1402_, 1, v___x_1399_);
        lean_ctor_set(v___x_1402_, 2, v___x_1401_);
        lean_ctor_set(v___x_1402_, 3, v___x_1344_);
        v___x_1403_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1349_,
            v___x_1349_,
            v___x_1402_,
        );
        v___x_1404_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61);
        v___x_1405_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62;
        v___x_1406_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1405_, v_currMacroScope_1328_);
        v___x_1407_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1407_, 0, v___x_1331_);
        lean_ctor_set(v___x_1407_, 1, v___x_1404_);
        lean_ctor_set(v___x_1407_, 2, v___x_1406_);
        lean_ctor_set(v___x_1407_, 3, v___x_1344_);
        v___x_1408_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1349_,
            v___x_1349_,
            v___x_1407_,
        );
        v___x_1409_ = lean_unsigned_to_nat(11);
        v___x_1410_ = lean_mk_empty_array_with_capacity(v___x_1409_);
        v___x_1411_ = lean_array_push(v___x_1410_, v___x_1376_);
        lean_inc_ref_n(v___x_1378_, 4);
        v___x_1412_ = lean_array_push(v___x_1411_, v___x_1378_);
        v___x_1413_ = lean_array_push(v___x_1412_, v___x_1388_);
        v___x_1414_ = lean_array_push(v___x_1413_, v___x_1378_);
        v___x_1415_ = lean_array_push(v___x_1414_, v___x_1394_);
        v___x_1416_ = lean_array_push(v___x_1415_, v___x_1378_);
        v___x_1417_ = lean_array_push(v___x_1416_, v___x_1398_);
        v___x_1418_ = lean_array_push(v___x_1417_, v___x_1378_);
        v___x_1419_ = lean_array_push(v___x_1418_, v___x_1403_);
        v___x_1420_ = lean_array_push(v___x_1419_, v___x_1378_);
        v___x_1421_ = lean_array_push(v___x_1420_, v___x_1408_);
        v___x_1422_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1422_, 0, v___x_1331_);
        lean_ctor_set(v___x_1422_, 1, v___x_1337_);
        lean_ctor_set(v___x_1422_, 2, v___x_1421_);
        v___x_1423_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63;
        v___x_1424_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1424_, 0, v___x_1331_);
        lean_ctor_set(v___x_1424_, 1, v___x_1423_);
        v___x_1425_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1337_,
            v___x_1369_,
            v___x_1422_,
            v___x_1424_,
        );
        v___x_1426_ = l_Lean_Syntax_node6(
            v___x_1331_,
            v___x_1361_,
            v___x_1362_,
            v___x_1364_,
            v___x_1349_,
            v___x_1367_,
            v___x_1425_,
            v___x_1349_,
        );
        v___x_1427_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1426_);
        v___x_1428_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1336_, v___x_1427_);
        v___x_1429_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1335_, v___x_1428_);
        v___x_1430_ = l_Lean_Syntax_node2(v___x_1331_, v___x_1357_, v___x_1359_, v___x_1429_);
        v___x_1431_ = l_Lean_Syntax_node5(
            v___x_1331_,
            v___x_1337_,
            v___x_1347_,
            v___x_1349_,
            v___x_1356_,
            v___x_1349_,
            v___x_1430_,
        );
        v___x_1432_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1336_, v___x_1431_);
        v___x_1433_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1335_, v___x_1432_);
        v___x_1434_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_1435_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1435_, 0, v___x_1331_);
        lean_ctor_set(v___x_1435_, 1, v___x_1434_);
        v___x_1436_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1332_,
            v___x_1334_,
            v___x_1433_,
            v___x_1435_,
        );
        v___x_1437_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1437_, 0, v___x_1436_);
        lean_ctor_set(v___x_1437_, 1, v_a_1322_);
        return v___x_1437_;
    }
}
pub unsafe fn l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___boxed(
    mut v_x_1438_: *mut LeanObject,
    mut v_a_1439_: *mut LeanObject,
    mut v_a_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1441_: *mut LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1(v_x_1438_, v_a_1439_, v_a_1440_);
    lean_dec_ref(v_a_1439_);
    return v_res_1441_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1(
    mut v_x_1464_: *mut LeanObject,
    mut v_a_1465_: *mut LeanObject,
    mut v_a_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: u8 = 0;
    v___x_1467_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_1468_ = l_Lean_Syntax_isOfKind(v_x_1464_, v___x_1467_);
    if v___x_1468_ == 0 {
        let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
        v___x_1469_ = lean_box(1);
        v___x_1470_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1470_, 0, v___x_1469_);
        lean_ctor_set(v___x_1470_, 1, v_a_1466_);
        return v___x_1470_;
    } else {
        let mut v_ref_1471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1472_: u8 = 0;
        let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
        v_ref_1471_ = lean_ctor_get(v_a_1465_, 5);
        v___x_1472_ = 0;
        v___x_1473_ = l_Lean_SourceInfo_fromRef(v_ref_1471_, v___x_1472_);
        v___x_1474_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0;
        v___x_1475_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1;
        lean_inc_n(v___x_1473_, 4);
        v___x_1476_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1476_, 0, v___x_1473_);
        lean_ctor_set(v___x_1476_, 1, v___x_1474_);
        v___x_1477_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_1478_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3;
        v___x_1479_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4;
        v___x_1480_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1480_, 0, v___x_1473_);
        lean_ctor_set(v___x_1480_, 1, v___x_1479_);
        v___x_1481_ = l_Lean_Syntax_node1(v___x_1473_, v___x_1478_, v___x_1480_);
        v___x_1482_ = l_Lean_Syntax_node1(v___x_1473_, v___x_1477_, v___x_1481_);
        v___x_1483_ = l_Lean_Syntax_node2(v___x_1473_, v___x_1475_, v___x_1476_, v___x_1482_);
        v___x_1484_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1484_, 0, v___x_1483_);
        lean_ctor_set(v___x_1484_, 1, v_a_1466_);
        return v___x_1484_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___boxed(
    mut v_x_1485_: *mut LeanObject,
    mut v_a_1486_: *mut LeanObject,
    mut v_a_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1488_: *mut LeanObject = core::ptr::null_mut();
    v_res_1488_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1(
            v_x_1485_, v_a_1486_, v_a_1487_,
        );
    lean_dec_ref(v_a_1486_);
    return v_res_1488_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13()
-> *mut LeanObject {
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    v___x_1519_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12;
    v___x_1520_ = l_String_toRawSubstring_x27(v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23()
-> *mut LeanObject {
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    v___x_1544_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22;
    v___x_1545_ = l_String_toRawSubstring_x27(v___x_1544_);
    return v___x_1545_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34()
-> *mut LeanObject {
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    v___x_1564_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33;
    v___x_1565_ = l_String_toRawSubstring_x27(v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43()
-> *mut LeanObject {
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    v___x_1585_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42;
    v___x_1586_ = l_String_toRawSubstring_x27(v___x_1585_);
    return v___x_1586_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67()
-> *mut LeanObject {
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    v___x_1631_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66;
    v___x_1632_ = l_String_toRawSubstring_x27(v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2(
    mut v_x_1647_: *mut LeanObject,
    mut v_a_1648_: *mut LeanObject,
    mut v_a_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    v___x_1650_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_1651_ = l_Lean_Syntax_isOfKind(v_x_1647_, v___x_1650_);
    if v___x_1651_ == 0 {
        let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
        v___x_1652_ = lean_box(1);
        v___x_1653_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1653_, 0, v___x_1652_);
        lean_ctor_set(v___x_1653_, 1, v_a_1649_);
        return v___x_1653_;
    } else {
        let mut v_quotContext_1654_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1655_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1656_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: u8 = 0;
        let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1654_ = lean_ctor_get(v_a_1648_, 1);
        v_currMacroScope_1655_ = lean_ctor_get(v_a_1648_, 2);
        v_ref_1656_ = lean_ctor_get(v_a_1648_, 5);
        v___x_1657_ = 0;
        v___x_1658_ = l_Lean_SourceInfo_fromRef(v_ref_1656_, v___x_1657_);
        v___x_1659_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_1660_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        lean_inc_n(v___x_1658_, 80);
        v___x_1661_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1661_, 0, v___x_1658_);
        lean_ctor_set(v___x_1661_, 1, v___x_1660_);
        v___x_1662_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_1663_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_1664_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_1665_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1;
        v___x_1666_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2;
        v___x_1667_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1667_, 0, v___x_1658_);
        lean_ctor_set(v___x_1667_, 1, v___x_1666_);
        v___x_1668_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3;
        v___x_1669_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4;
        v___x_1670_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1670_, 0, v___x_1658_);
        lean_ctor_set(v___x_1670_, 1, v___x_1668_);
        v___x_1671_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7;
        v___x_1672_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9;
        v___x_1673_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11;
        v___x_1674_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13);
        v___x_1675_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14;
        lean_inc_n(v_currMacroScope_1655_, 5);
        lean_inc_n(v_quotContext_1654_, 5);
        v___x_1676_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1675_, v_currMacroScope_1655_);
        v___x_1677_ = lean_box(0);
        v___x_1678_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16;
        v___x_1679_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1679_, 0, v___x_1658_);
        lean_ctor_set(v___x_1679_, 1, v___x_1674_);
        lean_ctor_set(v___x_1679_, 2, v___x_1676_);
        lean_ctor_set(v___x_1679_, 3, v___x_1678_);
        v___x_1680_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17;
        v___x_1681_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19;
        v___x_1682_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21;
        v___x_1683_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23);
        v___x_1684_ = lean_box(0);
        v___x_1685_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1684_, v_currMacroScope_1655_);
        v___x_1686_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25;
        v___x_1687_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1687_, 0, v___x_1658_);
        lean_ctor_set(v___x_1687_, 1, v___x_1683_);
        lean_ctor_set(v___x_1687_, 2, v___x_1685_);
        lean_ctor_set(v___x_1687_, 3, v___x_1686_);
        v___x_1688_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1682_, v___x_1687_);
        lean_inc_ref(v___x_1661_);
        v___x_1689_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1681_, v___x_1661_, v___x_1688_);
        v___x_1690_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27;
        v___x_1691_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29;
        v___x_1692_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30;
        v___x_1693_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1693_, 0, v___x_1658_);
        lean_ctor_set(v___x_1693_, 1, v___x_1692_);
        lean_inc_ref(v___x_1693_);
        v___x_1694_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1691_, v___x_1693_);
        v___x_1695_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31;
        v___x_1696_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1696_, 0, v___x_1658_);
        lean_ctor_set(v___x_1696_, 1, v___x_1695_);
        lean_inc_n(v___x_1694_, 4);
        v___x_1697_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1690_,
            v___x_1694_,
            v___x_1696_,
            v___x_1694_,
        );
        v___x_1698_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_1699_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1699_, 0, v___x_1658_);
        lean_ctor_set(v___x_1699_, 1, v___x_1698_);
        lean_inc_ref(v___x_1699_);
        v___x_1700_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1680_,
            v___x_1689_,
            v___x_1697_,
            v___x_1699_,
        );
        v___x_1701_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1664_,
            v___x_1700_,
            v___x_1694_,
            v___x_1694_,
        );
        v___x_1702_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1673_, v___x_1679_, v___x_1701_);
        v___x_1703_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32;
        v___x_1704_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1704_, 0, v___x_1658_);
        lean_ctor_set(v___x_1704_, 1, v___x_1703_);
        v___x_1705_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34);
        v___x_1706_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35;
        v___x_1707_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1706_, v_currMacroScope_1655_);
        v___x_1708_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38;
        v___x_1709_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1709_, 0, v___x_1658_);
        lean_ctor_set(v___x_1709_, 1, v___x_1705_);
        lean_ctor_set(v___x_1709_, 2, v___x_1707_);
        lean_ctor_set(v___x_1709_, 3, v___x_1708_);
        v___x_1710_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1672_,
            v___x_1702_,
            v___x_1704_,
            v___x_1709_,
        );
        v___x_1711_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39;
        v___x_1712_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1712_, 0, v___x_1658_);
        lean_ctor_set(v___x_1712_, 1, v___x_1711_);
        v___x_1713_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1671_,
            v___x_1710_,
            v___x_1712_,
            v___x_1694_,
        );
        v___x_1714_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_1715_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1715_, 0, v___x_1658_);
        lean_ctor_set(v___x_1715_, 1, v___x_1664_);
        lean_ctor_set(v___x_1715_, 2, v___x_1714_);
        lean_inc_ref_n(v___x_1715_, 19);
        v___x_1716_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1669_,
            v___x_1670_,
            v___x_1713_,
            v___x_1715_,
        );
        v___x_1717_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1716_);
        v___x_1718_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1717_);
        v___x_1719_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1718_);
        v___x_1720_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1665_, v___x_1667_, v___x_1719_);
        v___x_1721_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40;
        v___x_1722_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41;
        v___x_1723_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1723_, 0, v___x_1658_);
        lean_ctor_set(v___x_1723_, 1, v___x_1721_);
        v___x_1724_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43);
        v___x_1725_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45;
        v___x_1726_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1725_, v_currMacroScope_1655_);
        v___x_1727_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47;
        v___x_1728_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1728_, 0, v___x_1658_);
        lean_ctor_set(v___x_1728_, 1, v___x_1724_);
        lean_ctor_set(v___x_1728_, 2, v___x_1726_);
        lean_ctor_set(v___x_1728_, 3, v___x_1727_);
        v___x_1729_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49;
        v___x_1730_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50;
        v___x_1731_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1731_, 0, v___x_1658_);
        lean_ctor_set(v___x_1731_, 1, v___x_1730_);
        v___x_1732_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1729_, v___x_1731_, v___x_1693_);
        lean_inc(v___x_1732_);
        v___x_1733_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1664_, v___x_1732_, v___x_1732_);
        v___x_1734_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1673_, v___x_1728_, v___x_1733_);
        v___x_1735_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1722_, v___x_1723_, v___x_1734_);
        v___x_1736_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52;
        v___x_1737_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54;
        v___x_1738_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55;
        v___x_1739_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1739_, 0, v___x_1658_);
        lean_ctor_set(v___x_1739_, 1, v___x_1738_);
        v___x_1740_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1737_, v___x_1739_);
        v___x_1741_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57;
        v___x_1742_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58;
        v___x_1743_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1743_, 0, v___x_1658_);
        lean_ctor_set(v___x_1743_, 1, v___x_1742_);
        v___x_1744_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60;
        v___x_1745_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61;
        v___x_1746_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1746_, 0, v___x_1658_);
        lean_ctor_set(v___x_1746_, 1, v___x_1745_);
        v___x_1747_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63;
        v___x_1748_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64;
        v___x_1749_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1749_, 0, v___x_1658_);
        lean_ctor_set(v___x_1749_, 1, v___x_1748_);
        v___x_1750_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28;
        v___x_1751_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1750_, v___x_1715_);
        lean_inc_n(v___x_1751_, 2);
        v___x_1752_ = l_Lean_Syntax_node5(
            v___x_1658_,
            v___x_1747_,
            v___x_1749_,
            v___x_1751_,
            v___x_1715_,
            v___x_1715_,
            v___x_1715_,
        );
        v___x_1753_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1752_);
        v___x_1754_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1753_);
        v___x_1755_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1754_);
        lean_inc_ref_n(v___x_1746_, 2);
        v___x_1756_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1744_, v___x_1746_, v___x_1755_);
        v___x_1757_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25;
        v___x_1758_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26;
        v___x_1759_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1759_, 0, v___x_1658_);
        lean_ctor_set(v___x_1759_, 1, v___x_1757_);
        v___x_1760_ = l_Lean_Syntax_node6(
            v___x_1658_,
            v___x_1758_,
            v___x_1759_,
            v___x_1751_,
            v___x_1715_,
            v___x_1715_,
            v___x_1715_,
            v___x_1715_,
        );
        v___x_1761_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1760_);
        v___x_1762_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1761_);
        v___x_1763_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1762_);
        v___x_1764_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1744_, v___x_1746_, v___x_1763_);
        v___x_1765_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0;
        v___x_1766_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1;
        v___x_1767_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1767_, 0, v___x_1658_);
        lean_ctor_set(v___x_1767_, 1, v___x_1765_);
        v___x_1768_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3;
        v___x_1769_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65;
        v___x_1770_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1770_, 0, v___x_1658_);
        lean_ctor_set(v___x_1770_, 1, v___x_1769_);
        v___x_1771_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1768_, v___x_1770_);
        v___x_1772_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1771_);
        v___x_1773_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1766_, v___x_1767_, v___x_1772_);
        v___x_1774_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1773_);
        v___x_1775_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1774_);
        v___x_1776_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1775_);
        v___x_1777_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1744_, v___x_1746_, v___x_1776_);
        v___x_1778_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1664_,
            v___x_1756_,
            v___x_1764_,
            v___x_1777_,
        );
        v___x_1779_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1741_, v___x_1743_, v___x_1778_);
        v___x_1780_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1779_);
        v___x_1781_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1780_);
        v___x_1782_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1781_);
        v___x_1783_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1736_, v___x_1740_, v___x_1782_);
        v___x_1784_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_1785_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        v___x_1786_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1786_, 0, v___x_1658_);
        lean_ctor_set(v___x_1786_, 1, v___x_1784_);
        v___x_1787_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67);
        v___x_1788_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68;
        v___x_1789_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1788_, v_currMacroScope_1655_);
        v___x_1790_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1790_, 0, v___x_1658_);
        lean_ctor_set(v___x_1790_, 1, v___x_1787_);
        lean_ctor_set(v___x_1790_, 2, v___x_1789_);
        lean_ctor_set(v___x_1790_, 3, v___x_1677_);
        lean_inc_ref(v___x_1790_);
        v___x_1791_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1790_);
        v___x_1792_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1785_, v___x_1786_, v___x_1791_);
        v___x_1793_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69;
        v___x_1794_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70;
        v___x_1795_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1795_, 0, v___x_1658_);
        lean_ctor_set(v___x_1795_, 1, v___x_1793_);
        v___x_1796_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21;
        v___x_1797_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1796_, v___x_1715_, v___x_1790_);
        v___x_1798_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1797_);
        v___x_1799_ = l_Lean_Syntax_node4(
            v___x_1658_,
            v___x_1794_,
            v___x_1795_,
            v___x_1798_,
            v___x_1715_,
            v___x_1715_,
        );
        v___x_1800_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71;
        v___x_1801_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72;
        v___x_1802_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1802_, 0, v___x_1658_);
        lean_ctor_set(v___x_1802_, 1, v___x_1800_);
        v___x_1803_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29;
        v___x_1804_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1804_, 0, v___x_1658_);
        lean_ctor_set(v___x_1804_, 1, v___x_1803_);
        v___x_1805_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1804_);
        v___x_1806_ = l_Lean_Syntax_node6(
            v___x_1658_,
            v___x_1801_,
            v___x_1802_,
            v___x_1751_,
            v___x_1715_,
            v___x_1805_,
            v___x_1715_,
            v___x_1715_,
        );
        v___x_1807_ = lean_unsigned_to_nat(11);
        v___x_1808_ = lean_mk_empty_array_with_capacity(v___x_1807_);
        v___x_1809_ = lean_array_push(v___x_1808_, v___x_1720_);
        v___x_1810_ = lean_array_push(v___x_1809_, v___x_1715_);
        v___x_1811_ = lean_array_push(v___x_1810_, v___x_1735_);
        v___x_1812_ = lean_array_push(v___x_1811_, v___x_1715_);
        v___x_1813_ = lean_array_push(v___x_1812_, v___x_1783_);
        v___x_1814_ = lean_array_push(v___x_1813_, v___x_1715_);
        v___x_1815_ = lean_array_push(v___x_1814_, v___x_1792_);
        v___x_1816_ = lean_array_push(v___x_1815_, v___x_1715_);
        v___x_1817_ = lean_array_push(v___x_1816_, v___x_1799_);
        v___x_1818_ = lean_array_push(v___x_1817_, v___x_1715_);
        v___x_1819_ = lean_array_push(v___x_1818_, v___x_1806_);
        v___x_1820_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1820_, 0, v___x_1658_);
        lean_ctor_set(v___x_1820_, 1, v___x_1664_);
        lean_ctor_set(v___x_1820_, 2, v___x_1819_);
        v___x_1821_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1820_);
        v___x_1822_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1821_);
        v___x_1823_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1659_,
            v___x_1661_,
            v___x_1822_,
            v___x_1699_,
        );
        v___x_1824_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1824_, 0, v___x_1823_);
        lean_ctor_set(v___x_1824_, 1, v_a_1649_);
        return v___x_1824_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___boxed(
    mut v_x_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1828_: *mut LeanObject = core::ptr::null_mut();
    v_res_1828_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2(
            v_x_1825_, v_a_1826_, v_a_1827_,
        );
    lean_dec_ref(v_a_1826_);
    return v_res_1828_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4()
-> *mut LeanObject {
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    v___x_1839_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3;
    v___x_1840_ = l_String_toRawSubstring_x27(v___x_1839_);
    return v___x_1840_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3(
    mut v_x_1857_: *mut LeanObject,
    mut v_a_1858_: *mut LeanObject,
    mut v_a_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: u8 = 0;
    v___x_1860_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_1861_ = l_Lean_Syntax_isOfKind(v_x_1857_, v___x_1860_);
    if v___x_1861_ == 0 {
        let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
        v___x_1862_ = lean_box(1);
        v___x_1863_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1863_, 0, v___x_1862_);
        lean_ctor_set(v___x_1863_, 1, v_a_1859_);
        return v___x_1863_;
    } else {
        let mut v_quotContext_1864_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1865_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: u8 = 0;
        let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1864_ = lean_ctor_get(v_a_1858_, 1);
        v_currMacroScope_1865_ = lean_ctor_get(v_a_1858_, 2);
        v_ref_1866_ = lean_ctor_get(v_a_1858_, 5);
        v___x_1867_ = 0;
        v___x_1868_ = l_Lean_SourceInfo_fromRef(v_ref_1866_, v___x_1867_);
        v___x_1869_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_1870_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        lean_inc_n(v___x_1868_, 71);
        v___x_1871_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1871_, 0, v___x_1868_);
        lean_ctor_set(v___x_1871_, 1, v___x_1870_);
        v___x_1872_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_1873_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_1874_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_1875_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1;
        v___x_1876_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2;
        v___x_1877_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1877_, 0, v___x_1868_);
        lean_ctor_set(v___x_1877_, 1, v___x_1876_);
        v___x_1878_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3;
        v___x_1879_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4;
        v___x_1880_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1880_, 0, v___x_1868_);
        lean_ctor_set(v___x_1880_, 1, v___x_1878_);
        v___x_1881_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7;
        v___x_1882_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9;
        v___x_1883_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17;
        v___x_1884_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19;
        v___x_1885_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21;
        v___x_1886_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23);
        v___x_1887_ = lean_box(0);
        lean_inc_n(v_currMacroScope_1865_, 4);
        lean_inc_n(v_quotContext_1864_, 4);
        v___x_1888_ =
            l_Lean_addMacroScope(v_quotContext_1864_, v___x_1887_, v_currMacroScope_1865_);
        v___x_1889_ = lean_box(0);
        v___x_1890_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0;
        v___x_1891_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1891_, 0, v___x_1868_);
        lean_ctor_set(v___x_1891_, 1, v___x_1886_);
        lean_ctor_set(v___x_1891_, 2, v___x_1888_);
        lean_ctor_set(v___x_1891_, 3, v___x_1890_);
        v___x_1892_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1885_, v___x_1891_);
        lean_inc_ref(v___x_1871_);
        v___x_1893_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1884_, v___x_1871_, v___x_1892_);
        v___x_1894_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27;
        v___x_1895_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29;
        v___x_1896_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30;
        v___x_1897_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1897_, 0, v___x_1868_);
        lean_ctor_set(v___x_1897_, 1, v___x_1896_);
        lean_inc_ref(v___x_1897_);
        v___x_1898_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1895_, v___x_1897_);
        v___x_1899_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31;
        v___x_1900_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1900_, 0, v___x_1868_);
        lean_ctor_set(v___x_1900_, 1, v___x_1899_);
        lean_inc_n(v___x_1898_, 2);
        v___x_1901_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1894_,
            v___x_1898_,
            v___x_1900_,
            v___x_1898_,
        );
        v___x_1902_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_1903_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1903_, 0, v___x_1868_);
        lean_ctor_set(v___x_1903_, 1, v___x_1902_);
        lean_inc_ref(v___x_1903_);
        v___x_1904_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1883_,
            v___x_1893_,
            v___x_1901_,
            v___x_1903_,
        );
        v___x_1905_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32;
        v___x_1906_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1906_, 0, v___x_1868_);
        lean_ctor_set(v___x_1906_, 1, v___x_1905_);
        v___x_1907_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34);
        v___x_1908_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35;
        v___x_1909_ =
            l_Lean_addMacroScope(v_quotContext_1864_, v___x_1908_, v_currMacroScope_1865_);
        v___x_1910_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2;
        v___x_1911_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1911_, 0, v___x_1868_);
        lean_ctor_set(v___x_1911_, 1, v___x_1907_);
        lean_ctor_set(v___x_1911_, 2, v___x_1909_);
        lean_ctor_set(v___x_1911_, 3, v___x_1910_);
        v___x_1912_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1882_,
            v___x_1904_,
            v___x_1906_,
            v___x_1911_,
        );
        v___x_1913_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39;
        v___x_1914_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1914_, 0, v___x_1868_);
        lean_ctor_set(v___x_1914_, 1, v___x_1913_);
        v___x_1915_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1881_,
            v___x_1912_,
            v___x_1914_,
            v___x_1898_,
        );
        v___x_1916_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_1917_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1917_, 0, v___x_1868_);
        lean_ctor_set(v___x_1917_, 1, v___x_1874_);
        lean_ctor_set(v___x_1917_, 2, v___x_1916_);
        lean_inc_ref_n(v___x_1917_, 12);
        v___x_1918_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1879_,
            v___x_1880_,
            v___x_1915_,
            v___x_1917_,
        );
        v___x_1919_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1918_);
        v___x_1920_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1919_);
        v___x_1921_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1920_);
        v___x_1922_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1875_, v___x_1877_, v___x_1921_);
        v___x_1923_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40;
        v___x_1924_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41;
        v___x_1925_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1925_, 0, v___x_1868_);
        lean_ctor_set(v___x_1925_, 1, v___x_1923_);
        v___x_1926_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11;
        v___x_1927_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4);
        v___x_1928_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6;
        v___x_1929_ =
            l_Lean_addMacroScope(v_quotContext_1864_, v___x_1928_, v_currMacroScope_1865_);
        v___x_1930_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8;
        v___x_1931_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1931_, 0, v___x_1868_);
        lean_ctor_set(v___x_1931_, 1, v___x_1927_);
        lean_ctor_set(v___x_1931_, 2, v___x_1929_);
        lean_ctor_set(v___x_1931_, 3, v___x_1930_);
        v___x_1932_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49;
        v___x_1933_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50;
        v___x_1934_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1934_, 0, v___x_1868_);
        lean_ctor_set(v___x_1934_, 1, v___x_1933_);
        v___x_1935_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1932_, v___x_1934_, v___x_1897_);
        lean_inc(v___x_1935_);
        v___x_1936_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1874_, v___x_1935_, v___x_1935_);
        v___x_1937_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1926_, v___x_1931_, v___x_1936_);
        v___x_1938_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1924_, v___x_1925_, v___x_1937_);
        v___x_1939_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52;
        v___x_1940_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54;
        v___x_1941_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55;
        v___x_1942_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1942_, 0, v___x_1868_);
        lean_ctor_set(v___x_1942_, 1, v___x_1941_);
        v___x_1943_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1940_, v___x_1942_);
        v___x_1944_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57;
        v___x_1945_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58;
        v___x_1946_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1946_, 0, v___x_1868_);
        lean_ctor_set(v___x_1946_, 1, v___x_1945_);
        v___x_1947_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60;
        v___x_1948_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61;
        v___x_1949_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1949_, 0, v___x_1868_);
        lean_ctor_set(v___x_1949_, 1, v___x_1948_);
        v___x_1950_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63;
        v___x_1951_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64;
        v___x_1952_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1952_, 0, v___x_1868_);
        lean_ctor_set(v___x_1952_, 1, v___x_1951_);
        v___x_1953_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28;
        v___x_1954_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1953_, v___x_1917_);
        lean_inc(v___x_1954_);
        v___x_1955_ = l_Lean_Syntax_node5(
            v___x_1868_,
            v___x_1950_,
            v___x_1952_,
            v___x_1954_,
            v___x_1917_,
            v___x_1917_,
            v___x_1917_,
        );
        v___x_1956_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1955_);
        v___x_1957_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1956_);
        v___x_1958_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1957_);
        lean_inc_ref_n(v___x_1949_, 2);
        v___x_1959_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1947_, v___x_1949_, v___x_1958_);
        v___x_1960_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25;
        v___x_1961_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26;
        v___x_1962_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1962_, 0, v___x_1868_);
        lean_ctor_set(v___x_1962_, 1, v___x_1960_);
        v___x_1963_ = l_Lean_Syntax_node6(
            v___x_1868_,
            v___x_1961_,
            v___x_1962_,
            v___x_1954_,
            v___x_1917_,
            v___x_1917_,
            v___x_1917_,
            v___x_1917_,
        );
        v___x_1964_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1963_);
        v___x_1965_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1964_);
        v___x_1966_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1965_);
        v___x_1967_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1947_, v___x_1949_, v___x_1966_);
        v___x_1968_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0;
        v___x_1969_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1;
        v___x_1970_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1970_, 0, v___x_1868_);
        lean_ctor_set(v___x_1970_, 1, v___x_1968_);
        v___x_1971_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3;
        v___x_1972_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65;
        v___x_1973_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1973_, 0, v___x_1868_);
        lean_ctor_set(v___x_1973_, 1, v___x_1972_);
        v___x_1974_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1971_, v___x_1973_);
        v___x_1975_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1974_);
        v___x_1976_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1969_, v___x_1970_, v___x_1975_);
        v___x_1977_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1976_);
        v___x_1978_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1977_);
        v___x_1979_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1978_);
        v___x_1980_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1947_, v___x_1949_, v___x_1979_);
        v___x_1981_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1874_,
            v___x_1959_,
            v___x_1967_,
            v___x_1980_,
        );
        v___x_1982_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1944_, v___x_1946_, v___x_1981_);
        v___x_1983_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1982_);
        v___x_1984_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1983_);
        v___x_1985_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1984_);
        v___x_1986_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1939_, v___x_1943_, v___x_1985_);
        v___x_1987_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_1988_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        v___x_1989_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1989_, 0, v___x_1868_);
        lean_ctor_set(v___x_1989_, 1, v___x_1987_);
        v___x_1990_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67);
        v___x_1991_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68;
        v___x_1992_ =
            l_Lean_addMacroScope(v_quotContext_1864_, v___x_1991_, v_currMacroScope_1865_);
        v___x_1993_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1993_, 0, v___x_1868_);
        lean_ctor_set(v___x_1993_, 1, v___x_1990_);
        lean_ctor_set(v___x_1993_, 2, v___x_1992_);
        lean_ctor_set(v___x_1993_, 3, v___x_1889_);
        v___x_1994_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1993_);
        lean_inc(v___x_1994_);
        v___x_1995_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1988_, v___x_1989_, v___x_1994_);
        v___x_1996_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9;
        v___x_1997_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10;
        v___x_1998_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_1998_, 0, v___x_1868_);
        lean_ctor_set(v___x_1998_, 1, v___x_1996_);
        v___x_1999_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1997_, v___x_1998_, v___x_1994_);
        v___x_2000_ = lean_unsigned_to_nat(9);
        v___x_2001_ = lean_mk_empty_array_with_capacity(v___x_2000_);
        v___x_2002_ = lean_array_push(v___x_2001_, v___x_1922_);
        v___x_2003_ = lean_array_push(v___x_2002_, v___x_1917_);
        v___x_2004_ = lean_array_push(v___x_2003_, v___x_1938_);
        v___x_2005_ = lean_array_push(v___x_2004_, v___x_1917_);
        v___x_2006_ = lean_array_push(v___x_2005_, v___x_1986_);
        v___x_2007_ = lean_array_push(v___x_2006_, v___x_1917_);
        v___x_2008_ = lean_array_push(v___x_2007_, v___x_1995_);
        v___x_2009_ = lean_array_push(v___x_2008_, v___x_1917_);
        v___x_2010_ = lean_array_push(v___x_2009_, v___x_1999_);
        v___x_2011_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2011_, 0, v___x_1868_);
        lean_ctor_set(v___x_2011_, 1, v___x_1874_);
        lean_ctor_set(v___x_2011_, 2, v___x_2010_);
        v___x_2012_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_2011_);
        v___x_2013_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_2012_);
        v___x_2014_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1869_,
            v___x_1871_,
            v___x_2013_,
            v___x_1903_,
        );
        v___x_2015_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2015_, 0, v___x_2014_);
        lean_ctor_set(v___x_2015_, 1, v_a_1859_);
        return v___x_2015_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___boxed(
    mut v_x_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2019_: *mut LeanObject = core::ptr::null_mut();
    v_res_2019_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3(
            v_x_2016_, v_a_2017_, v_a_2018_,
        );
    lean_dec_ref(v_a_2017_);
    return v_res_2019_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4()
-> *mut LeanObject {
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    v___x_2025_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3;
    v___x_2026_ = l_String_toRawSubstring_x27(v___x_2025_);
    return v___x_2026_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4(
    mut v_x_2037_: *mut LeanObject,
    mut v_a_2038_: *mut LeanObject,
    mut v_a_2039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: u8 = 0;
    v___x_2040_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_2041_ = l_Lean_Syntax_isOfKind(v_x_2037_, v___x_2040_);
    if v___x_2041_ == 0 {
        let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
        v___x_2042_ = lean_box(1);
        v___x_2043_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2043_, 0, v___x_2042_);
        lean_ctor_set(v___x_2043_, 1, v_a_2039_);
        return v___x_2043_;
    } else {
        let mut v_quotContext_2044_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2045_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: u8 = 0;
        let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2044_ = lean_ctor_get(v_a_2038_, 1);
        v_currMacroScope_2045_ = lean_ctor_get(v_a_2038_, 2);
        v_ref_2046_ = lean_ctor_get(v_a_2038_, 5);
        v___x_2047_ = 0;
        v___x_2048_ = l_Lean_SourceInfo_fromRef(v_ref_2046_, v___x_2047_);
        v___x_2049_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_2050_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        lean_inc_n(v___x_2048_, 35);
        v___x_2051_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2051_, 0, v___x_2048_);
        lean_ctor_set(v___x_2051_, 1, v___x_2050_);
        v___x_2052_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_2053_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_2054_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_2055_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1;
        v___x_2056_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2;
        v___x_2057_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2057_, 0, v___x_2048_);
        lean_ctor_set(v___x_2057_, 1, v___x_2056_);
        v___x_2058_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3;
        v___x_2059_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4;
        v___x_2060_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2060_, 0, v___x_2048_);
        lean_ctor_set(v___x_2060_, 1, v___x_2058_);
        v___x_2061_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7;
        v___x_2062_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9;
        v___x_2063_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17;
        v___x_2064_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19;
        v___x_2065_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21;
        v___x_2066_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23);
        v___x_2067_ = lean_box(0);
        lean_inc_n(v_currMacroScope_2045_, 3);
        lean_inc_n(v_quotContext_2044_, 3);
        v___x_2068_ =
            l_Lean_addMacroScope(v_quotContext_2044_, v___x_2067_, v_currMacroScope_2045_);
        v___x_2069_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0;
        v___x_2070_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2070_, 0, v___x_2048_);
        lean_ctor_set(v___x_2070_, 1, v___x_2066_);
        lean_ctor_set(v___x_2070_, 2, v___x_2068_);
        lean_ctor_set(v___x_2070_, 3, v___x_2069_);
        v___x_2071_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2065_, v___x_2070_);
        lean_inc_ref(v___x_2051_);
        v___x_2072_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2064_, v___x_2051_, v___x_2071_);
        v___x_2073_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1;
        v___x_2074_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27;
        v___x_2075_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29;
        v___x_2076_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30;
        v___x_2077_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2077_, 0, v___x_2048_);
        lean_ctor_set(v___x_2077_, 1, v___x_2076_);
        lean_inc_ref(v___x_2077_);
        v___x_2078_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2075_, v___x_2077_);
        v___x_2079_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31;
        v___x_2080_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2080_, 0, v___x_2048_);
        lean_ctor_set(v___x_2080_, 1, v___x_2079_);
        lean_inc_n(v___x_2078_, 3);
        v___x_2081_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2074_,
            v___x_2078_,
            v___x_2080_,
            v___x_2078_,
        );
        v___x_2082_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2;
        v___x_2083_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2083_, 0, v___x_2048_);
        lean_ctor_set(v___x_2083_, 1, v___x_2082_);
        v___x_2084_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2073_,
            v___x_2081_,
            v___x_2083_,
            v___x_2078_,
        );
        v___x_2085_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_2086_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2086_, 0, v___x_2048_);
        lean_ctor_set(v___x_2086_, 1, v___x_2085_);
        lean_inc_ref(v___x_2086_);
        v___x_2087_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2063_,
            v___x_2072_,
            v___x_2084_,
            v___x_2086_,
        );
        v___x_2088_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32;
        v___x_2089_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2089_, 0, v___x_2048_);
        lean_ctor_set(v___x_2089_, 1, v___x_2088_);
        v___x_2090_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34);
        v___x_2091_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35;
        v___x_2092_ =
            l_Lean_addMacroScope(v_quotContext_2044_, v___x_2091_, v_currMacroScope_2045_);
        v___x_2093_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2;
        v___x_2094_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2094_, 0, v___x_2048_);
        lean_ctor_set(v___x_2094_, 1, v___x_2090_);
        lean_ctor_set(v___x_2094_, 2, v___x_2092_);
        lean_ctor_set(v___x_2094_, 3, v___x_2093_);
        v___x_2095_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2062_,
            v___x_2087_,
            v___x_2089_,
            v___x_2094_,
        );
        v___x_2096_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39;
        v___x_2097_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2097_, 0, v___x_2048_);
        lean_ctor_set(v___x_2097_, 1, v___x_2096_);
        v___x_2098_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2061_,
            v___x_2095_,
            v___x_2097_,
            v___x_2078_,
        );
        v___x_2099_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_2100_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2100_, 0, v___x_2048_);
        lean_ctor_set(v___x_2100_, 1, v___x_2054_);
        lean_ctor_set(v___x_2100_, 2, v___x_2099_);
        lean_inc_ref(v___x_2100_);
        v___x_2101_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2059_,
            v___x_2060_,
            v___x_2098_,
            v___x_2100_,
        );
        v___x_2102_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2054_, v___x_2101_);
        v___x_2103_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2053_, v___x_2102_);
        v___x_2104_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2052_, v___x_2103_);
        v___x_2105_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2055_, v___x_2057_, v___x_2104_);
        v___x_2106_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40;
        v___x_2107_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41;
        v___x_2108_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2108_, 0, v___x_2048_);
        lean_ctor_set(v___x_2108_, 1, v___x_2106_);
        v___x_2109_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11;
        v___x_2110_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4);
        v___x_2111_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6;
        v___x_2112_ =
            l_Lean_addMacroScope(v_quotContext_2044_, v___x_2111_, v_currMacroScope_2045_);
        v___x_2113_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8;
        v___x_2114_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2114_, 0, v___x_2048_);
        lean_ctor_set(v___x_2114_, 1, v___x_2110_);
        lean_ctor_set(v___x_2114_, 2, v___x_2112_);
        lean_ctor_set(v___x_2114_, 3, v___x_2113_);
        v___x_2115_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49;
        v___x_2116_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50;
        v___x_2117_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2117_, 0, v___x_2048_);
        lean_ctor_set(v___x_2117_, 1, v___x_2116_);
        v___x_2118_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2115_, v___x_2117_, v___x_2077_);
        v___x_2119_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2054_, v___x_2118_);
        v___x_2120_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2109_, v___x_2114_, v___x_2119_);
        v___x_2121_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2107_, v___x_2108_, v___x_2120_);
        v___x_2122_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2054_,
            v___x_2105_,
            v___x_2100_,
            v___x_2121_,
        );
        v___x_2123_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2053_, v___x_2122_);
        v___x_2124_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2052_, v___x_2123_);
        v___x_2125_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2049_,
            v___x_2051_,
            v___x_2124_,
            v___x_2086_,
        );
        v___x_2126_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2126_, 0, v___x_2125_);
        lean_ctor_set(v___x_2126_, 1, v_a_2039_);
        return v___x_2126_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___boxed(
    mut v_x_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
    mut v_a_2129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2130_: *mut LeanObject = core::ptr::null_mut();
    v_res_2130_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4(
            v_x_2127_, v_a_2128_, v_a_2129_,
        );
    lean_dec_ref(v_a_2128_);
    return v_res_2130_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5(
    mut v_x_2138_: *mut LeanObject,
    mut v_a_2139_: *mut LeanObject,
    mut v_a_2140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: u8 = 0;
    v___x_2141_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_2142_ = l_Lean_Syntax_isOfKind(v_x_2138_, v___x_2141_);
    if v___x_2142_ == 0 {
        let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
        v___x_2143_ = lean_box(1);
        v___x_2144_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2144_, 0, v___x_2143_);
        lean_ctor_set(v___x_2144_, 1, v_a_2140_);
        return v___x_2144_;
    } else {
        let mut v_ref_2145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: u8 = 0;
        let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
        v_ref_2145_ = lean_ctor_get(v_a_2139_, 5);
        v___x_2146_ = 0;
        v___x_2147_ = l_Lean_SourceInfo_fromRef(v_ref_2145_, v___x_2146_);
        v___x_2148_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1;
        v___x_2149_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2;
        lean_inc(v___x_2147_);
        v___x_2150_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2150_, 0, v___x_2147_);
        lean_ctor_set(v___x_2150_, 1, v___x_2149_);
        v___x_2151_ = l_Lean_Syntax_node1(v___x_2147_, v___x_2148_, v___x_2150_);
        v___x_2152_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2152_, 0, v___x_2151_);
        lean_ctor_set(v___x_2152_, 1, v_a_2140_);
        return v___x_2152_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___boxed(
    mut v_x_2153_: *mut LeanObject,
    mut v_a_2154_: *mut LeanObject,
    mut v_a_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2156_: *mut LeanObject = core::ptr::null_mut();
    v_res_2156_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5(
            v_x_2153_, v_a_2154_, v_a_2155_,
        );
    lean_dec_ref(v_a_2154_);
    return v_res_2156_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6(
    mut v_x_2171_: *mut LeanObject,
    mut v_a_2172_: *mut LeanObject,
    mut v_a_2173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    v___x_2174_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_2175_ = l_Lean_Syntax_isOfKind(v_x_2171_, v___x_2174_);
    if v___x_2175_ == 0 {
        let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
        v___x_2176_ = lean_box(1);
        v___x_2177_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2177_, 0, v___x_2176_);
        lean_ctor_set(v___x_2177_, 1, v_a_2173_);
        return v___x_2177_;
    } else {
        let mut v_ref_2178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2179_: u8 = 0;
        let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
        v_ref_2178_ = lean_ctor_get(v_a_2172_, 5);
        v___x_2179_ = 0;
        v___x_2180_ = l_Lean_SourceInfo_fromRef(v_ref_2178_, v___x_2179_);
        v___x_2181_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1;
        v___x_2182_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_2183_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_2184_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        lean_inc_n(v___x_2180_, 9);
        v___x_2185_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2185_, 0, v___x_2180_);
        lean_ctor_set(v___x_2185_, 1, v___x_2183_);
        v___x_2186_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29;
        v___x_2187_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30;
        v___x_2188_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2188_, 0, v___x_2180_);
        lean_ctor_set(v___x_2188_, 1, v___x_2187_);
        v___x_2189_ = l_Lean_Syntax_node1(v___x_2180_, v___x_2186_, v___x_2188_);
        v___x_2190_ = l_Lean_Syntax_node1(v___x_2180_, v___x_2182_, v___x_2189_);
        v___x_2191_ = l_Lean_Syntax_node2(v___x_2180_, v___x_2184_, v___x_2185_, v___x_2190_);
        v___x_2192_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2;
        v___x_2193_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2193_, 0, v___x_2180_);
        lean_ctor_set(v___x_2193_, 1, v___x_2192_);
        v___x_2194_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4;
        v___x_2195_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5;
        v___x_2196_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2196_, 0, v___x_2180_);
        lean_ctor_set(v___x_2196_, 1, v___x_2195_);
        v___x_2197_ = l_Lean_Syntax_node1(v___x_2180_, v___x_2194_, v___x_2196_);
        v___x_2198_ = l_Lean_Syntax_node3(
            v___x_2180_,
            v___x_2182_,
            v___x_2191_,
            v___x_2193_,
            v___x_2197_,
        );
        v___x_2199_ = l_Lean_Syntax_node1(v___x_2180_, v___x_2181_, v___x_2198_);
        v___x_2200_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2200_, 0, v___x_2199_);
        lean_ctor_set(v___x_2200_, 1, v_a_2173_);
        return v___x_2200_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___boxed(
    mut v_x_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2204_: *mut LeanObject = core::ptr::null_mut();
    v_res_2204_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6(
            v_x_2201_, v_a_2202_, v_a_2203_,
        );
    lean_dec_ref(v_a_2202_);
    return v_res_2204_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    v___x_2218_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0;
    v___x_2219_ = l_String_toRawSubstring_x27(v___x_2218_);
    return v___x_2219_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1(
    mut v_x_2229_: *mut LeanObject,
    mut v_a_2230_: *mut LeanObject,
    mut v_a_2231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: u8 = 0;
    v___x_2232_ = l_tacticDeriving__LawfulEq__tactic___closed__1;
    v___x_2233_ = l_Lean_Syntax_isOfKind(v_x_2229_, v___x_2232_);
    if v___x_2233_ == 0 {
        let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
        v___x_2234_ = lean_box(1);
        v___x_2235_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2235_, 0, v___x_2234_);
        lean_ctor_set(v___x_2235_, 1, v_a_2231_);
        return v___x_2235_;
    } else {
        let mut v_quotContext_2236_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2237_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: u8 = 0;
        let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2236_ = lean_ctor_get(v_a_2230_, 1);
        v_currMacroScope_2237_ = lean_ctor_get(v_a_2230_, 2);
        v_ref_2238_ = lean_ctor_get(v_a_2230_, 5);
        v___x_2239_ = 0;
        v___x_2240_ = l_Lean_SourceInfo_fromRef(v_ref_2238_, v___x_2239_);
        v___x_2241_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_2242_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        lean_inc_n(v___x_2240_, 51);
        v___x_2243_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2243_, 0, v___x_2240_);
        lean_ctor_set(v___x_2243_, 1, v___x_2242_);
        v___x_2244_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_2245_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_2246_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_2247_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_2248_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        v___x_2249_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2249_, 0, v___x_2240_);
        lean_ctor_set(v___x_2249_, 1, v___x_2247_);
        v___x_2250_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15);
        v___x_2251_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16;
        lean_inc_n(v_currMacroScope_2237_, 4);
        lean_inc_n(v_quotContext_2236_, 4);
        v___x_2252_ =
            l_Lean_addMacroScope(v_quotContext_2236_, v___x_2251_, v_currMacroScope_2237_);
        v___x_2253_ = lean_box(0);
        v___x_2254_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2254_, 0, v___x_2240_);
        lean_ctor_set(v___x_2254_, 1, v___x_2250_);
        lean_ctor_set(v___x_2254_, 2, v___x_2252_);
        lean_ctor_set(v___x_2254_, 3, v___x_2253_);
        lean_inc_ref(v___x_2254_);
        v___x_2255_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2254_);
        lean_inc_ref(v___x_2249_);
        v___x_2256_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2248_, v___x_2249_, v___x_2255_);
        v___x_2257_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_2258_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2258_, 0, v___x_2240_);
        lean_ctor_set(v___x_2258_, 1, v___x_2246_);
        lean_ctor_set(v___x_2258_, 2, v___x_2257_);
        v___x_2259_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18;
        v___x_2260_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19;
        v___x_2261_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2261_, 0, v___x_2240_);
        lean_ctor_set(v___x_2261_, 1, v___x_2259_);
        v___x_2262_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21;
        lean_inc_ref_n(v___x_2258_, 18);
        v___x_2263_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2262_, v___x_2258_, v___x_2254_);
        v___x_2264_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2263_);
        v___x_2265_ = l_Lean_Syntax_node5(
            v___x_2240_,
            v___x_2260_,
            v___x_2261_,
            v___x_2264_,
            v___x_2258_,
            v___x_2258_,
            v___x_2258_,
        );
        v___x_2266_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23;
        v___x_2267_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24;
        v___x_2268_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2268_, 0, v___x_2240_);
        lean_ctor_set(v___x_2268_, 1, v___x_2267_);
        v___x_2269_ = lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1);
        v___x_2270_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2;
        v___x_2271_ =
            l_Lean_addMacroScope(v_quotContext_2236_, v___x_2270_, v_currMacroScope_2237_);
        v___x_2272_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2272_, 0, v___x_2240_);
        lean_ctor_set(v___x_2272_, 1, v___x_2269_);
        lean_ctor_set(v___x_2272_, 2, v___x_2271_);
        lean_ctor_set(v___x_2272_, 3, v___x_2253_);
        lean_inc_ref(v___x_2272_);
        v___x_2273_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2272_);
        v___x_2274_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2248_, v___x_2249_, v___x_2273_);
        v___x_2275_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69;
        v___x_2276_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70;
        v___x_2277_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2277_, 0, v___x_2240_);
        lean_ctor_set(v___x_2277_, 1, v___x_2275_);
        v___x_2278_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2262_, v___x_2258_, v___x_2272_);
        v___x_2279_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2278_);
        v___x_2280_ = l_Lean_Syntax_node4(
            v___x_2240_,
            v___x_2276_,
            v___x_2277_,
            v___x_2279_,
            v___x_2258_,
            v___x_2258_,
        );
        v___x_2281_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25;
        v___x_2282_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26;
        v___x_2283_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2283_, 0, v___x_2240_);
        lean_ctor_set(v___x_2283_, 1, v___x_2281_);
        v___x_2284_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28;
        v___x_2285_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2284_, v___x_2258_);
        v___x_2286_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29;
        v___x_2287_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2287_, 0, v___x_2240_);
        lean_ctor_set(v___x_2287_, 1, v___x_2286_);
        v___x_2288_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2287_);
        v___x_2289_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30;
        v___x_2290_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2290_, 0, v___x_2240_);
        lean_ctor_set(v___x_2290_, 1, v___x_2289_);
        v___x_2291_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32;
        v___x_2292_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58);
        v___x_2293_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59;
        v___x_2294_ =
            l_Lean_addMacroScope(v_quotContext_2236_, v___x_2293_, v_currMacroScope_2237_);
        v___x_2295_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2295_, 0, v___x_2240_);
        lean_ctor_set(v___x_2295_, 1, v___x_2292_);
        lean_ctor_set(v___x_2295_, 2, v___x_2294_);
        lean_ctor_set(v___x_2295_, 3, v___x_2253_);
        v___x_2296_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2291_,
            v___x_2258_,
            v___x_2258_,
            v___x_2295_,
        );
        v___x_2297_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40;
        v___x_2298_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2298_, 0, v___x_2240_);
        lean_ctor_set(v___x_2298_, 1, v___x_2297_);
        v___x_2299_ = lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61);
        v___x_2300_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62;
        v___x_2301_ =
            l_Lean_addMacroScope(v_quotContext_2236_, v___x_2300_, v_currMacroScope_2237_);
        v___x_2302_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2302_, 0, v___x_2240_);
        lean_ctor_set(v___x_2302_, 1, v___x_2299_);
        lean_ctor_set(v___x_2302_, 2, v___x_2301_);
        lean_ctor_set(v___x_2302_, 3, v___x_2253_);
        v___x_2303_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2291_,
            v___x_2258_,
            v___x_2258_,
            v___x_2302_,
        );
        v___x_2304_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2246_,
            v___x_2296_,
            v___x_2298_,
            v___x_2303_,
        );
        v___x_2305_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63;
        v___x_2306_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2306_, 0, v___x_2240_);
        lean_ctor_set(v___x_2306_, 1, v___x_2305_);
        v___x_2307_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2246_,
            v___x_2290_,
            v___x_2304_,
            v___x_2306_,
        );
        v___x_2308_ = l_Lean_Syntax_node6(
            v___x_2240_,
            v___x_2282_,
            v___x_2283_,
            v___x_2285_,
            v___x_2258_,
            v___x_2288_,
            v___x_2307_,
            v___x_2258_,
        );
        v___x_2309_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4;
        v___x_2310_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5;
        v___x_2311_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2311_, 0, v___x_2240_);
        lean_ctor_set(v___x_2311_, 1, v___x_2310_);
        v___x_2312_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
        v___x_2313_ = l_tacticDeriving__LawfulEq__tactic__step___closed__2;
        v___x_2314_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2314_, 0, v___x_2240_);
        lean_ctor_set(v___x_2314_, 1, v___x_2313_);
        v___x_2315_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2312_, v___x_2314_);
        v___x_2316_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2315_);
        v___x_2317_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2245_, v___x_2316_);
        v___x_2318_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2244_, v___x_2317_);
        v___x_2319_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2309_, v___x_2311_, v___x_2318_);
        v___x_2320_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2246_,
            v___x_2308_,
            v___x_2258_,
            v___x_2319_,
        );
        v___x_2321_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2245_, v___x_2320_);
        v___x_2322_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2244_, v___x_2321_);
        lean_inc_ref(v___x_2268_);
        v___x_2323_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2266_, v___x_2268_, v___x_2322_);
        v___x_2324_ = l_Lean_Syntax_node5(
            v___x_2240_,
            v___x_2246_,
            v___x_2274_,
            v___x_2258_,
            v___x_2280_,
            v___x_2258_,
            v___x_2323_,
        );
        v___x_2325_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2245_, v___x_2324_);
        v___x_2326_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2244_, v___x_2325_);
        v___x_2327_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2266_, v___x_2268_, v___x_2326_);
        v___x_2328_ = l_Lean_Syntax_node5(
            v___x_2240_,
            v___x_2246_,
            v___x_2256_,
            v___x_2258_,
            v___x_2265_,
            v___x_2258_,
            v___x_2327_,
        );
        v___x_2329_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2245_, v___x_2328_);
        v___x_2330_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2244_, v___x_2329_);
        v___x_2331_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_2332_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2332_, 0, v___x_2240_);
        lean_ctor_set(v___x_2332_, 1, v___x_2331_);
        v___x_2333_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2241_,
            v___x_2243_,
            v___x_2330_,
            v___x_2332_,
        );
        v___x_2334_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2334_, 0, v___x_2333_);
        lean_ctor_set(v___x_2334_, 1, v_a_2231_);
        return v___x_2334_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___boxed(
    mut v_x_2335_: *mut LeanObject,
    mut v_a_2336_: *mut LeanObject,
    mut v_a_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2338_: *mut LeanObject = core::ptr::null_mut();
    v_res_2338_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1(
            v_x_2335_, v_a_2336_, v_a_2337_,
        );
    lean_dec_ref(v_a_2336_);
    return v_res_2338_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_LawfulBEqTactics(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Data_Bool(builtin);
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
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_LawfulBEqTactics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_LawfulBEqTactics(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_Data_Bool(builtin);
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
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_LawfulBEqTactics(builtin);
}
