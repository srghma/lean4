// Lean compiler output
// Module: Init.Data.Iterators.Basic
// Imports: Init.NotationExtra Init.WFTactics Init.Ext Init.PropLemmas
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
pub static l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114, 105, 118, 105, 97, 108, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut crate::leanh::LeanObject,5744670087858236374 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 114, 115, 116, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut crate::leanh::LeanObject,12551601070224435259 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__7_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__9_value) as *mut crate::leanh::LeanObject,2214559063752339918 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__12_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__14_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16_value) as *mut crate::leanh::LeanObject,14997215300048349804 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__19_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [73, 116, 101, 114, 77, 46, 84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 77, 101, 97, 115, 117, 114, 101, 115, 46, 70, 105, 110, 105, 116, 101, 46, 114, 101, 108, 95, 111, 102, 95, 121, 105, 101, 108, 100, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 116, 101, 114, 77, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 77, 101, 97, 115, 117, 114, 101, 115, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [70, 105, 110, 105, 116, 101, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [114, 101, 108, 95, 111, 102, 95, 121, 105, 101, 108, 100, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,1959508619676314626 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,5246936068696429737 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject,17344145950358906317 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut crate::leanh::LeanObject,1978584141957904254 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,13664751295710188101 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,5938245225010022570 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject,3295385452655174498 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut crate::leanh::LeanObject,76670523031171933 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__30_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__29_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__30_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__32_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 7, m_data: [116, 101, 114, 109, 226, 128, 185, 95, 226, 128, 186, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject,8315864120963730325 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 128, 185, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__35_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__35_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__35_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 128, 186, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39_value: crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [73, 116, 101, 114, 77, 46, 84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 77, 101, 97, 115, 117, 114, 101, 115, 46, 70, 105, 110, 105, 116, 101, 46, 114, 101, 108, 95, 111, 102, 95, 115, 107, 105, 112, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [114, 101, 108, 95, 111, 102, 95, 115, 107, 105, 112, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,1959508619676314626 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,5246936068696429737 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject,17344145950358906317 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject,16798535429797319532 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,13664751295710188101 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,5938245225010022570 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject,3295385452655174498 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject,17827289293850724879 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__44_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__43_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__44_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [102, 97, 105, 108, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46_value) as *mut crate::leanh::LeanObject,59994724629665531 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0_value: crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [73, 116, 101, 114, 46, 84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 77, 101, 97, 115, 117, 114, 101, 115, 46, 70, 105, 110, 105, 116, 101, 46, 114, 101, 108, 95, 111, 102, 95, 121, 105, 101, 108, 100, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [73, 116, 101, 114, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,16200121334493070218 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,10443658743878322129 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject,11293238081452519989 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut crate::leanh::LeanObject,14309352849202144982 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,10311657911549824541 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,16231970142106159074 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject,2101613656138220154 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut crate::leanh::LeanObject,160844810344822021 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7_value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [73, 116, 101, 114, 46, 84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 77, 101, 97, 115, 117, 114, 101, 115, 46, 70, 105, 110, 105, 116, 101, 46, 114, 101, 108, 95, 111, 102, 95, 115, 107, 105, 112, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,16200121334493070218 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,10443658743878322129 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject,11293238081452519989 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject,3724227993359000724 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,10311657911549824541 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,16231970142106159074 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject,2101613656138220154 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject,184120074493047399 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0_value: crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [73, 116, 101, 114, 77, 46, 84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 77, 101, 97, 115, 117, 114, 101, 115, 46, 80, 114, 111, 100, 117, 99, 116, 105, 118, 101, 46, 114, 101, 108, 95, 111, 102, 95, 115, 107, 105, 112, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [80, 114, 111, 100, 117, 99, 116, 105, 118, 101, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,1959508619676314626 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,5246936068696429737 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value) as *mut crate::leanh::LeanObject,12853073183624429938 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject,3826270375831763647 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,13664751295710188101 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,5938245225010022570 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value) as *mut crate::leanh::LeanObject,10836681387012277213 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject,2621144765333685276 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [73, 116, 101, 114, 46, 84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 77, 101, 97, 115, 117, 114, 101, 115, 46, 80, 114, 111, 100, 117, 99, 116, 105, 118, 101, 46, 114, 101, 108, 95, 111, 102, 95, 115, 107, 105, 112, 0]};
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,16200121334493070218 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,10443658743878322129 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value) as *mut crate::leanh::LeanObject,7493099670341267898 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject,7528470458661005095 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__28_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,10311657911549824541 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,16231970142106159074 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__2_value) as *mut crate::leanh::LeanObject,12257681512842486133 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject,15121431985942316116 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0(
    mut v___y_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___y_1023_);
    return v___y_1023_;
}
pub unsafe fn l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0___boxed(
    mut v___y_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1025_ =
        l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___lam__0(v___y_1024_);
    crate::leanh::lean_dec(v___y_1024_);
    return v_res_1025_;
}
pub unsafe fn l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque(
    mut v_00_u03b1_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1028_ = l___private_Init_Data_Iterators_Basic_0__Std_Internal_idOpaque___closed__0;
    return v___f_1028_;
}
pub unsafe fn l_Std_Shrink_deflate___redArg(
    mut v_x_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1029_);
    return v_x_1029_;
}
pub unsafe fn l_Std_Shrink_deflate___redArg___boxed(
    mut v_x_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l_Std_Shrink_deflate___redArg(v_x_1030_);
    crate::leanh::lean_dec(v_x_1030_);
    return v_res_1031_;
}
pub unsafe fn l_Std_Shrink_deflate(
    mut v_00_u03b1_1032_: *mut crate::leanh::LeanObject,
    mut v_x_1033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1033_);
    return v_x_1033_;
}
pub unsafe fn l_Std_Shrink_deflate___boxed(
    mut v_00_u03b1_1034_: *mut crate::leanh::LeanObject,
    mut v_x_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Std_Shrink_deflate(v_00_u03b1_1034_, v_x_1035_);
    crate::leanh::lean_dec(v_x_1035_);
    return v_res_1036_;
}
pub unsafe fn l_Std_Shrink_inflate___redArg(
    mut v_x_1037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1037_);
    return v_x_1037_;
}
pub unsafe fn l_Std_Shrink_inflate___redArg___boxed(
    mut v_x_1038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Std_Shrink_inflate___redArg(v_x_1038_);
    crate::leanh::lean_dec(v_x_1038_);
    return v_res_1039_;
}
pub unsafe fn l_Std_Shrink_inflate(
    mut v_00_u03b1_1040_: *mut crate::leanh::LeanObject,
    mut v_x_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1041_);
    return v_x_1041_;
}
pub unsafe fn l_Std_Shrink_inflate___boxed(
    mut v_00_u03b1_1042_: *mut crate::leanh::LeanObject,
    mut v_x_1043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1044_ = l_Std_Shrink_inflate(v_00_u03b1_1042_, v_x_1043_);
    crate::leanh::lean_dec(v_x_1043_);
    return v_res_1044_;
}
pub unsafe fn l_Std_Iter_toIterM___redArg(
    mut v_it_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1045_);
    return v_it_1045_;
}
pub unsafe fn l_Std_Iter_toIterM___redArg___boxed(
    mut v_it_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Std_Iter_toIterM___redArg(v_it_1046_);
    crate::leanh::lean_dec(v_it_1046_);
    return v_res_1047_;
}
pub unsafe fn l_Std_Iter_toIterM(
    mut v_00_u03b1_1048_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1049_: *mut crate::leanh::LeanObject,
    mut v_it_1050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1050_);
    return v_it_1050_;
}
pub unsafe fn l_Std_Iter_toIterM___boxed(
    mut v_00_u03b1_1051_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1052_: *mut crate::leanh::LeanObject,
    mut v_it_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Std_Iter_toIterM(v_00_u03b1_1051_, v_00_u03b2_1052_, v_it_1053_);
    crate::leanh::lean_dec(v_it_1053_);
    return v_res_1054_;
}
pub unsafe fn l_Std_IterM_toIter___redArg(
    mut v_it_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1055_);
    return v_it_1055_;
}
pub unsafe fn l_Std_IterM_toIter___redArg___boxed(
    mut v_it_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ = l_Std_IterM_toIter___redArg(v_it_1056_);
    crate::leanh::lean_dec(v_it_1056_);
    return v_res_1057_;
}
pub unsafe fn l_Std_IterM_toIter(
    mut v_00_u03b1_1058_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1059_: *mut crate::leanh::LeanObject,
    mut v_it_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1060_);
    return v_it_1060_;
}
pub unsafe fn l_Std_IterM_toIter___boxed(
    mut v_00_u03b1_1061_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1062_: *mut crate::leanh::LeanObject,
    mut v_it_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Std_IterM_toIter(v_00_u03b1_1061_, v_00_u03b2_1062_, v_it_1063_);
    crate::leanh::lean_dec(v_it_1063_);
    return v_res_1064_;
}
pub unsafe fn l_Std_IterStep_ctorIdx___redArg(
    mut v_x_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1065_) {
        0 => {
            let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1066_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1066_;
        }
        1 => {
            let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1067_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1067_;
        }
        _ => {
            let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1068_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1068_;
        }
    }
}
pub unsafe fn l_Std_IterStep_ctorIdx___redArg___boxed(
    mut v_x_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1070_ = l_Std_IterStep_ctorIdx___redArg(v_x_1069_);
    crate::leanh::lean_dec(v_x_1069_);
    return v_res_1070_;
}
pub unsafe fn l_Std_IterStep_ctorIdx(
    mut v_00_u03b1_1071_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1072_: *mut crate::leanh::LeanObject,
    mut v_x_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = l_Std_IterStep_ctorIdx___redArg(v_x_1073_);
    return v___x_1074_;
}
pub unsafe fn l_Std_IterStep_ctorIdx___boxed(
    mut v_00_u03b1_1075_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1076_: *mut crate::leanh::LeanObject,
    mut v_x_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Std_IterStep_ctorIdx(v_00_u03b1_1075_, v_00_u03b2_1076_, v_x_1077_);
    crate::leanh::lean_dec(v_x_1077_);
    return v_res_1078_;
}
pub unsafe fn l_Std_IterStep_ctorElim___redArg(
    mut v_t_1079_: *mut crate::leanh::LeanObject,
    mut v_k_1080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1079_) {
        0 => {
            let mut v_it_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_1081_ = crate::leanh::lean_ctor_get(v_t_1079_, 0);
            crate::leanh::lean_inc(v_it_1081_);
            v_out_1082_ = crate::leanh::lean_ctor_get(v_t_1079_, 1);
            crate::leanh::lean_inc(v_out_1082_);
            crate::leanh::lean_dec_ref_known(v_t_1079_, 2);
            v___x_1083_ = crate::leanh::lean_apply_2(v_k_1080_, v_it_1081_, v_out_1082_);
            return v___x_1083_;
        }
        1 => {
            let mut v_it_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_1084_ = crate::leanh::lean_ctor_get(v_t_1079_, 0);
            crate::leanh::lean_inc(v_it_1084_);
            crate::leanh::lean_dec_ref_known(v_t_1079_, 1);
            v___x_1085_ = crate::leanh::lean_apply_1(v_k_1080_, v_it_1084_);
            return v___x_1085_;
        }
        _ => {
            return v_k_1080_;
        }
    }
}
pub unsafe fn l_Std_IterStep_ctorElim(
    mut v_00_u03b1_1086_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1087_: *mut crate::leanh::LeanObject,
    mut v_motive_1088_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1089_: *mut crate::leanh::LeanObject,
    mut v_t_1090_: *mut crate::leanh::LeanObject,
    mut v_h_1091_: *mut crate::leanh::LeanObject,
    mut v_k_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = l_Std_IterStep_ctorElim___redArg(v_t_1090_, v_k_1092_);
    return v___x_1093_;
}
pub unsafe fn l_Std_IterStep_ctorElim___boxed(
    mut v_00_u03b1_1094_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1095_: *mut crate::leanh::LeanObject,
    mut v_motive_1096_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1097_: *mut crate::leanh::LeanObject,
    mut v_t_1098_: *mut crate::leanh::LeanObject,
    mut v_h_1099_: *mut crate::leanh::LeanObject,
    mut v_k_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1101_ = l_Std_IterStep_ctorElim(
        v_00_u03b1_1094_,
        v_00_u03b2_1095_,
        v_motive_1096_,
        v_ctorIdx_1097_,
        v_t_1098_,
        v_h_1099_,
        v_k_1100_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1097_);
    return v_res_1101_;
}
pub unsafe fn l_Std_IterStep_yield_elim___redArg(
    mut v_t_1102_: *mut crate::leanh::LeanObject,
    mut v_yield_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = l_Std_IterStep_ctorElim___redArg(v_t_1102_, v_yield_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Std_IterStep_yield_elim(
    mut v_00_u03b1_1105_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1106_: *mut crate::leanh::LeanObject,
    mut v_motive_1107_: *mut crate::leanh::LeanObject,
    mut v_t_1108_: *mut crate::leanh::LeanObject,
    mut v_h_1109_: *mut crate::leanh::LeanObject,
    mut v_yield_1110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1111_ = l_Std_IterStep_ctorElim___redArg(v_t_1108_, v_yield_1110_);
    return v___x_1111_;
}
pub unsafe fn l_Std_IterStep_skip_elim___redArg(
    mut v_t_1112_: *mut crate::leanh::LeanObject,
    mut v_skip_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = l_Std_IterStep_ctorElim___redArg(v_t_1112_, v_skip_1113_);
    return v___x_1114_;
}
pub unsafe fn l_Std_IterStep_skip_elim(
    mut v_00_u03b1_1115_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1116_: *mut crate::leanh::LeanObject,
    mut v_motive_1117_: *mut crate::leanh::LeanObject,
    mut v_t_1118_: *mut crate::leanh::LeanObject,
    mut v_h_1119_: *mut crate::leanh::LeanObject,
    mut v_skip_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Std_IterStep_ctorElim___redArg(v_t_1118_, v_skip_1120_);
    return v___x_1121_;
}
pub unsafe fn l_Std_IterStep_done_elim___redArg(
    mut v_t_1122_: *mut crate::leanh::LeanObject,
    mut v_done_1123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1124_ = l_Std_IterStep_ctorElim___redArg(v_t_1122_, v_done_1123_);
    return v___x_1124_;
}
pub unsafe fn l_Std_IterStep_done_elim(
    mut v_00_u03b1_1125_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1126_: *mut crate::leanh::LeanObject,
    mut v_motive_1127_: *mut crate::leanh::LeanObject,
    mut v_t_1128_: *mut crate::leanh::LeanObject,
    mut v_h_1129_: *mut crate::leanh::LeanObject,
    mut v_done_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = l_Std_IterStep_ctorElim___redArg(v_t_1128_, v_done_1130_);
    return v___x_1131_;
}
pub unsafe fn l_Std_IterStep_successor___redArg(
    mut v_x_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1138_: u8 = 0;
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1142_: u8 = 0;
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1132_) {
                0 => {
                    v_it_1133_ = crate::leanh::lean_ctor_get(v_x_1132_, 0);
                    crate::leanh::lean_inc(v_it_1133_);
                    crate::leanh::lean_dec_ref_known(v_x_1132_, 2);
                    v___x_1134_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1134_, 0, v_it_1133_);
                    return v___x_1134_;
                }
                1 => {
                    v_it_1135_ = crate::leanh::lean_ctor_get(v_x_1132_, 0);
                    v_isSharedCheck_1142_ = (!crate::leanh::lean_is_exclusive(v_x_1132_)) as u8;
                    if v_isSharedCheck_1142_ == 0 {
                        v___x_1137_ = v_x_1132_;
                        v_isShared_1138_ = v_isSharedCheck_1142_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_1135_);
                        crate::leanh::lean_dec(v_x_1132_);
                        v___x_1137_ = crate::leanh::lean_box(0);
                        v_isShared_1138_ = v_isSharedCheck_1142_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v___x_1143_ = crate::leanh::lean_box(0);
                    return v___x_1143_;
                }
            },
            1 => {
                if v_isShared_1138_ == 0 {
                    v___x_1140_ = v___x_1137_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_it_1135_);
                    v___x_1140_ = v_reuseFailAlloc_1141_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterStep_successor(
    mut v_00_u03b1_1144_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1145_: *mut crate::leanh::LeanObject,
    mut v_x_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1147_ = l_Std_IterStep_successor___redArg(v_x_1146_);
    return v___x_1147_;
}
pub unsafe fn l_Std_IterStep_mapIterator___redArg(
    mut v_f_1148_: *mut crate::leanh::LeanObject,
    mut v_x_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1154_: u8 = 0;
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1159_: u8 = 0;
    let mut v_it_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1168_: u8 = 0;
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1149_) {
                0 => {
                    v_it_1150_ = crate::leanh::lean_ctor_get(v_x_1149_, 0);
                    v_out_1151_ = crate::leanh::lean_ctor_get(v_x_1149_, 1);
                    v_isSharedCheck_1159_ = (!crate::leanh::lean_is_exclusive(v_x_1149_)) as u8;
                    if v_isSharedCheck_1159_ == 0 {
                        v___x_1153_ = v_x_1149_;
                        v_isShared_1154_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_1151_);
                        crate::leanh::lean_inc(v_it_1150_);
                        crate::leanh::lean_dec(v_x_1149_);
                        v___x_1153_ = crate::leanh::lean_box(0);
                        v_isShared_1154_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_1160_ = crate::leanh::lean_ctor_get(v_x_1149_, 0);
                    v_isSharedCheck_1168_ = (!crate::leanh::lean_is_exclusive(v_x_1149_)) as u8;
                    if v_isSharedCheck_1168_ == 0 {
                        v___x_1162_ = v_x_1149_;
                        v_isShared_1163_ = v_isSharedCheck_1168_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_1160_);
                        crate::leanh::lean_dec(v_x_1149_);
                        v___x_1162_ = crate::leanh::lean_box(0);
                        v_isShared_1163_ = v_isSharedCheck_1168_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_f_1148_);
                    v___x_1169_ = crate::leanh::lean_box(2);
                    return v___x_1169_;
                }
            },
            1 => {
                v___x_1155_ = crate::leanh::lean_apply_1(v_f_1148_, v_it_1150_);
                if v_isShared_1154_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1153_, 0, v___x_1155_);
                    v___x_1157_ = v___x_1153_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1158_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_out_1151_);
                    v___x_1157_ = v_reuseFailAlloc_1158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1157_;
            }
            3 => {
                v___x_1164_ = crate::leanh::lean_apply_1(v_f_1148_, v_it_1160_);
                if v_isShared_1163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1164_);
                    v___x_1166_ = v___x_1162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
                    v___x_1166_ = v_reuseFailAlloc_1167_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterStep_mapIterator(
    mut v_00_u03b1_1170_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1171_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_x27_1172_: *mut crate::leanh::LeanObject,
    mut v_f_1173_: *mut crate::leanh::LeanObject,
    mut v_x_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1179_: u8 = 0;
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1184_: u8 = 0;
    let mut v_it_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1188_: u8 = 0;
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1193_: u8 = 0;
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1174_) {
                0 => {
                    v_it_1175_ = crate::leanh::lean_ctor_get(v_x_1174_, 0);
                    v_out_1176_ = crate::leanh::lean_ctor_get(v_x_1174_, 1);
                    v_isSharedCheck_1184_ = (!crate::leanh::lean_is_exclusive(v_x_1174_)) as u8;
                    if v_isSharedCheck_1184_ == 0 {
                        v___x_1178_ = v_x_1174_;
                        v_isShared_1179_ = v_isSharedCheck_1184_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_1176_);
                        crate::leanh::lean_inc(v_it_1175_);
                        crate::leanh::lean_dec(v_x_1174_);
                        v___x_1178_ = crate::leanh::lean_box(0);
                        v_isShared_1179_ = v_isSharedCheck_1184_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_1185_ = crate::leanh::lean_ctor_get(v_x_1174_, 0);
                    v_isSharedCheck_1193_ = (!crate::leanh::lean_is_exclusive(v_x_1174_)) as u8;
                    if v_isSharedCheck_1193_ == 0 {
                        v___x_1187_ = v_x_1174_;
                        v_isShared_1188_ = v_isSharedCheck_1193_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_1185_);
                        crate::leanh::lean_dec(v_x_1174_);
                        v___x_1187_ = crate::leanh::lean_box(0);
                        v_isShared_1188_ = v_isSharedCheck_1193_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_f_1173_);
                    v___x_1194_ = crate::leanh::lean_box(2);
                    return v___x_1194_;
                }
            },
            1 => {
                v___x_1180_ = crate::leanh::lean_apply_1(v_f_1173_, v_it_1175_);
                if v_isShared_1179_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1178_, 0, v___x_1180_);
                    v___x_1182_ = v___x_1178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_out_1176_);
                    v___x_1182_ = v_reuseFailAlloc_1183_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1182_;
            }
            3 => {
                v___x_1189_ = crate::leanh::lean_apply_1(v_f_1173_, v_it_1185_);
                if v_isShared_1188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1187_, 0, v___x_1189_);
                    v___x_1191_ = v___x_1187_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
                    v___x_1191_ = v_reuseFailAlloc_1192_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_PlausibleIterStep_yield___redArg(
    mut v_it_x27_1195_: *mut crate::leanh::LeanObject,
    mut v_out_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1197_, 0, v_it_x27_1195_);
    crate::leanh::lean_ctor_set(v___x_1197_, 1, v_out_1196_);
    return v___x_1197_;
}
pub unsafe fn l_Std_PlausibleIterStep_yield(
    mut v_00_u03b1_1198_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1199_: *mut crate::leanh::LeanObject,
    mut v_IsPlausibleStep_1200_: *mut crate::leanh::LeanObject,
    mut v_it_x27_1201_: *mut crate::leanh::LeanObject,
    mut v_out_1202_: *mut crate::leanh::LeanObject,
    mut v_h_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1204_, 0, v_it_x27_1201_);
    crate::leanh::lean_ctor_set(v___x_1204_, 1, v_out_1202_);
    return v___x_1204_;
}
pub unsafe fn l_Std_PlausibleIterStep_skip___redArg(
    mut v_it_x27_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1206_, 0, v_it_x27_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Std_PlausibleIterStep_skip(
    mut v_00_u03b1_1207_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1208_: *mut crate::leanh::LeanObject,
    mut v_IsPlausibleStep_1209_: *mut crate::leanh::LeanObject,
    mut v_it_x27_1210_: *mut crate::leanh::LeanObject,
    mut v_h_1211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1212_, 0, v_it_x27_1210_);
    return v___x_1212_;
}
pub unsafe fn l_Std_PlausibleIterStep_done(
    mut v_00_u03b1_1213_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1214_: *mut crate::leanh::LeanObject,
    mut v_IsPlausibleStep_1215_: *mut crate::leanh::LeanObject,
    mut v_h_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = crate::leanh::lean_box(2);
    return v___x_1217_;
}
pub unsafe fn l_Std_PlausibleIterStep_casesOn___redArg(
    mut v_s_1218_: *mut crate::leanh::LeanObject,
    mut v_yield_1219_: *mut crate::leanh::LeanObject,
    mut v_skip_1220_: *mut crate::leanh::LeanObject,
    mut v_done_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_1218_) {
        0 => {
            let mut v_it_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_done_1221_);
            crate::leanh::lean_dec(v_skip_1220_);
            v_it_1222_ = crate::leanh::lean_ctor_get(v_s_1218_, 0);
            crate::leanh::lean_inc(v_it_1222_);
            v_out_1223_ = crate::leanh::lean_ctor_get(v_s_1218_, 1);
            crate::leanh::lean_inc(v_out_1223_);
            crate::leanh::lean_dec_ref_known(v_s_1218_, 2);
            v___x_1224_ = crate::leanh::lean_apply_3(
                v_yield_1219_,
                v_it_1222_,
                v_out_1223_,
                crate::leanh::lean_box(0),
            );
            return v___x_1224_;
        }
        1 => {
            let mut v_it_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_done_1221_);
            crate::leanh::lean_dec(v_yield_1219_);
            v_it_1225_ = crate::leanh::lean_ctor_get(v_s_1218_, 0);
            crate::leanh::lean_inc(v_it_1225_);
            crate::leanh::lean_dec_ref_known(v_s_1218_, 1);
            v___x_1226_ =
                crate::leanh::lean_apply_2(v_skip_1220_, v_it_1225_, crate::leanh::lean_box(0));
            return v___x_1226_;
        }
        _ => {
            let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_skip_1220_);
            crate::leanh::lean_dec(v_yield_1219_);
            v___x_1227_ = crate::leanh::lean_apply_1(v_done_1221_, crate::leanh::lean_box(0));
            return v___x_1227_;
        }
    }
}
pub unsafe fn l_Std_PlausibleIterStep_casesOn(
    mut v_00_u03b1_1228_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1229_: *mut crate::leanh::LeanObject,
    mut v_IsPlausibleStep_1230_: *mut crate::leanh::LeanObject,
    mut v_motive_1231_: *mut crate::leanh::LeanObject,
    mut v_s_1232_: *mut crate::leanh::LeanObject,
    mut v_yield_1233_: *mut crate::leanh::LeanObject,
    mut v_skip_1234_: *mut crate::leanh::LeanObject,
    mut v_done_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_1232_) {
        0 => {
            let mut v_it_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_done_1235_);
            crate::leanh::lean_dec(v_skip_1234_);
            v_it_1236_ = crate::leanh::lean_ctor_get(v_s_1232_, 0);
            crate::leanh::lean_inc(v_it_1236_);
            v_out_1237_ = crate::leanh::lean_ctor_get(v_s_1232_, 1);
            crate::leanh::lean_inc(v_out_1237_);
            crate::leanh::lean_dec_ref_known(v_s_1232_, 2);
            v___x_1238_ = crate::leanh::lean_apply_3(
                v_yield_1233_,
                v_it_1236_,
                v_out_1237_,
                crate::leanh::lean_box(0),
            );
            return v___x_1238_;
        }
        1 => {
            let mut v_it_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_done_1235_);
            crate::leanh::lean_dec(v_yield_1233_);
            v_it_1239_ = crate::leanh::lean_ctor_get(v_s_1232_, 0);
            crate::leanh::lean_inc(v_it_1239_);
            crate::leanh::lean_dec_ref_known(v_s_1232_, 1);
            v___x_1240_ =
                crate::leanh::lean_apply_2(v_skip_1234_, v_it_1239_, crate::leanh::lean_box(0));
            return v___x_1240_;
        }
        _ => {
            let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_skip_1234_);
            crate::leanh::lean_dec(v_yield_1233_);
            v___x_1241_ = crate::leanh::lean_apply_1(v_done_1235_, crate::leanh::lean_box(0));
            return v___x_1241_;
        }
    }
}
pub unsafe fn l_Std_IterM_mk_x27___redArg(
    mut v_it_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1242_);
    return v_it_1242_;
}
pub unsafe fn l_Std_IterM_mk_x27___redArg___boxed(
    mut v_it_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1244_ = l_Std_IterM_mk_x27___redArg(v_it_1243_);
    crate::leanh::lean_dec(v_it_1243_);
    return v_res_1244_;
}
pub unsafe fn l_Std_IterM_mk_x27(
    mut v_00_u03b1_1245_: *mut crate::leanh::LeanObject,
    mut v_m_1246_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1247_: *mut crate::leanh::LeanObject,
    mut v_it_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1248_);
    return v_it_1248_;
}
pub unsafe fn l_Std_IterM_mk_x27___boxed(
    mut v_00_u03b1_1249_: *mut crate::leanh::LeanObject,
    mut v_m_1250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1251_: *mut crate::leanh::LeanObject,
    mut v_it_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1253_ = l_Std_IterM_mk_x27(v_00_u03b1_1249_, v_m_1250_, v_00_u03b2_1251_, v_it_1252_);
    crate::leanh::lean_dec(v_it_1252_);
    return v_res_1253_;
}
pub unsafe fn l_Std_Iterators_toIterM___redArg(
    mut v_internalState_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_internalState_1254_);
    return v_internalState_1254_;
}
pub unsafe fn l_Std_Iterators_toIterM___redArg___boxed(
    mut v_internalState_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1256_ = l_Std_Iterators_toIterM___redArg(v_internalState_1255_);
    crate::leanh::lean_dec(v_internalState_1255_);
    return v_res_1256_;
}
pub unsafe fn l_Std_Iterators_toIterM(
    mut v_00_u03b1_1257_: *mut crate::leanh::LeanObject,
    mut v_m_1258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1259_: *mut crate::leanh::LeanObject,
    mut v_internalState_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_internalState_1260_);
    return v_internalState_1260_;
}
pub unsafe fn l_Std_Iterators_toIterM___boxed(
    mut v_00_u03b1_1261_: *mut crate::leanh::LeanObject,
    mut v_m_1262_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1263_: *mut crate::leanh::LeanObject,
    mut v_internalState_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Std_Iterators_toIterM(
        v_00_u03b1_1261_,
        v_m_1262_,
        v_00_u03b2_1263_,
        v_internalState_1264_,
    );
    crate::leanh::lean_dec(v_internalState_1264_);
    return v_res_1265_;
}
pub unsafe fn l_Std_IterM_step___redArg(
    mut v_inst_1266_: *mut crate::leanh::LeanObject,
    mut v_it_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1268_ = crate::leanh::lean_apply_1(v_inst_1266_, v_it_1267_);
    return v___x_1268_;
}
pub unsafe fn l_Std_IterM_step(
    mut v_00_u03b1_1269_: *mut crate::leanh::LeanObject,
    mut v_m_1270_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1271_: *mut crate::leanh::LeanObject,
    mut v_inst_1272_: *mut crate::leanh::LeanObject,
    mut v_it_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = crate::leanh::lean_apply_1(v_inst_1272_, v_it_1273_);
    return v___x_1274_;
}
pub unsafe fn l_Std_Iter_Step_toMonadic___redArg(
    mut v_step_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1280_: u8 = 0;
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut v_it_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_step_1275_) {
                0 => {
                    v_it_1276_ = crate::leanh::lean_ctor_get(v_step_1275_, 0);
                    v_out_1277_ = crate::leanh::lean_ctor_get(v_step_1275_, 1);
                    v_isSharedCheck_1284_ = (!crate::leanh::lean_is_exclusive(v_step_1275_)) as u8;
                    if v_isSharedCheck_1284_ == 0 {
                        v___x_1279_ = v_step_1275_;
                        v_isShared_1280_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_1277_);
                        crate::leanh::lean_inc(v_it_1276_);
                        crate::leanh::lean_dec(v_step_1275_);
                        v___x_1279_ = crate::leanh::lean_box(0);
                        v_isShared_1280_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_1285_ = crate::leanh::lean_ctor_get(v_step_1275_, 0);
                    v_isSharedCheck_1292_ = (!crate::leanh::lean_is_exclusive(v_step_1275_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1287_ = v_step_1275_;
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_1285_);
                        crate::leanh::lean_dec(v_step_1275_);
                        v___x_1287_ = crate::leanh::lean_box(0);
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_1293_ = crate::leanh::lean_box(2);
                    return v___x_1293_;
                }
            },
            1 => {
                if v_isShared_1280_ == 0 {
                    v___x_1282_ = v___x_1279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_it_1276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_out_1277_);
                    v___x_1282_ = v_reuseFailAlloc_1283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1282_;
            }
            3 => {
                if v_isShared_1288_ == 0 {
                    v___x_1290_ = v___x_1287_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_it_1285_);
                    v___x_1290_ = v_reuseFailAlloc_1291_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iter_Step_toMonadic(
    mut v_00_u03b1_1294_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1295_: *mut crate::leanh::LeanObject,
    mut v_inst_1296_: *mut crate::leanh::LeanObject,
    mut v_it_1297_: *mut crate::leanh::LeanObject,
    mut v_step_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1303_: u8 = 0;
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut v_it_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1315_: u8 = 0;
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_step_1298_) {
                0 => {
                    v_it_1299_ = crate::leanh::lean_ctor_get(v_step_1298_, 0);
                    v_out_1300_ = crate::leanh::lean_ctor_get(v_step_1298_, 1);
                    v_isSharedCheck_1307_ = (!crate::leanh::lean_is_exclusive(v_step_1298_)) as u8;
                    if v_isSharedCheck_1307_ == 0 {
                        v___x_1302_ = v_step_1298_;
                        v_isShared_1303_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_1300_);
                        crate::leanh::lean_inc(v_it_1299_);
                        crate::leanh::lean_dec(v_step_1298_);
                        v___x_1302_ = crate::leanh::lean_box(0);
                        v_isShared_1303_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_1308_ = crate::leanh::lean_ctor_get(v_step_1298_, 0);
                    v_isSharedCheck_1315_ = (!crate::leanh::lean_is_exclusive(v_step_1298_)) as u8;
                    if v_isSharedCheck_1315_ == 0 {
                        v___x_1310_ = v_step_1298_;
                        v_isShared_1311_ = v_isSharedCheck_1315_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_1308_);
                        crate::leanh::lean_dec(v_step_1298_);
                        v___x_1310_ = crate::leanh::lean_box(0);
                        v_isShared_1311_ = v_isSharedCheck_1315_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_1316_ = crate::leanh::lean_box(2);
                    return v___x_1316_;
                }
            },
            1 => {
                if v_isShared_1303_ == 0 {
                    v___x_1305_ = v___x_1302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_it_1299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_out_1300_);
                    v___x_1305_ = v_reuseFailAlloc_1306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1305_;
            }
            3 => {
                if v_isShared_1311_ == 0 {
                    v___x_1313_ = v___x_1310_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1314_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_it_1308_);
                    v___x_1313_ = v_reuseFailAlloc_1314_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iter_Step_toMonadic___boxed(
    mut v_00_u03b1_1317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1318_: *mut crate::leanh::LeanObject,
    mut v_inst_1319_: *mut crate::leanh::LeanObject,
    mut v_it_1320_: *mut crate::leanh::LeanObject,
    mut v_step_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Std_Iter_Step_toMonadic(
        v_00_u03b1_1317_,
        v_00_u03b2_1318_,
        v_inst_1319_,
        v_it_1320_,
        v_step_1321_,
    );
    crate::leanh::lean_dec(v_it_1320_);
    crate::leanh::lean_dec(v_inst_1319_);
    return v_res_1322_;
}
pub unsafe fn l_Std_IterM_Step_toPure___redArg(
    mut v_step_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1332_: u8 = 0;
    let mut v_it_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1336_: u8 = 0;
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1340_: u8 = 0;
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_step_1323_) {
                0 => {
                    v_it_1324_ = crate::leanh::lean_ctor_get(v_step_1323_, 0);
                    v_out_1325_ = crate::leanh::lean_ctor_get(v_step_1323_, 1);
                    v_isSharedCheck_1332_ = (!crate::leanh::lean_is_exclusive(v_step_1323_)) as u8;
                    if v_isSharedCheck_1332_ == 0 {
                        v___x_1327_ = v_step_1323_;
                        v_isShared_1328_ = v_isSharedCheck_1332_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_1325_);
                        crate::leanh::lean_inc(v_it_1324_);
                        crate::leanh::lean_dec(v_step_1323_);
                        v___x_1327_ = crate::leanh::lean_box(0);
                        v_isShared_1328_ = v_isSharedCheck_1332_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_1333_ = crate::leanh::lean_ctor_get(v_step_1323_, 0);
                    v_isSharedCheck_1340_ = (!crate::leanh::lean_is_exclusive(v_step_1323_)) as u8;
                    if v_isSharedCheck_1340_ == 0 {
                        v___x_1335_ = v_step_1323_;
                        v_isShared_1336_ = v_isSharedCheck_1340_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_1333_);
                        crate::leanh::lean_dec(v_step_1323_);
                        v___x_1335_ = crate::leanh::lean_box(0);
                        v_isShared_1336_ = v_isSharedCheck_1340_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_1341_ = crate::leanh::lean_box(2);
                    return v___x_1341_;
                }
            },
            1 => {
                if v_isShared_1328_ == 0 {
                    v___x_1330_ = v___x_1327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_it_1324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_out_1325_);
                    v___x_1330_ = v_reuseFailAlloc_1331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1330_;
            }
            3 => {
                if v_isShared_1336_ == 0 {
                    v___x_1338_ = v___x_1335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_it_1333_);
                    v___x_1338_ = v_reuseFailAlloc_1339_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterM_Step_toPure(
    mut v_00_u03b1_1342_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1343_: *mut crate::leanh::LeanObject,
    mut v_inst_1344_: *mut crate::leanh::LeanObject,
    mut v_it_1345_: *mut crate::leanh::LeanObject,
    mut v_step_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_it_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_step_1346_) {
                0 => {
                    v_it_1347_ = crate::leanh::lean_ctor_get(v_step_1346_, 0);
                    v_out_1348_ = crate::leanh::lean_ctor_get(v_step_1346_, 1);
                    v_isSharedCheck_1355_ = (!crate::leanh::lean_is_exclusive(v_step_1346_)) as u8;
                    if v_isSharedCheck_1355_ == 0 {
                        v___x_1350_ = v_step_1346_;
                        v_isShared_1351_ = v_isSharedCheck_1355_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_1348_);
                        crate::leanh::lean_inc(v_it_1347_);
                        crate::leanh::lean_dec(v_step_1346_);
                        v___x_1350_ = crate::leanh::lean_box(0);
                        v_isShared_1351_ = v_isSharedCheck_1355_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_1356_ = crate::leanh::lean_ctor_get(v_step_1346_, 0);
                    v_isSharedCheck_1363_ = (!crate::leanh::lean_is_exclusive(v_step_1346_)) as u8;
                    if v_isSharedCheck_1363_ == 0 {
                        v___x_1358_ = v_step_1346_;
                        v_isShared_1359_ = v_isSharedCheck_1363_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_1356_);
                        crate::leanh::lean_dec(v_step_1346_);
                        v___x_1358_ = crate::leanh::lean_box(0);
                        v_isShared_1359_ = v_isSharedCheck_1363_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_1364_ = crate::leanh::lean_box(2);
                    return v___x_1364_;
                }
            },
            1 => {
                if v_isShared_1351_ == 0 {
                    v___x_1353_ = v___x_1350_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_it_1347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_out_1348_);
                    v___x_1353_ = v_reuseFailAlloc_1354_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1353_;
            }
            3 => {
                if v_isShared_1359_ == 0 {
                    v___x_1361_ = v___x_1358_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_it_1356_);
                    v___x_1361_ = v_reuseFailAlloc_1362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterM_Step_toPure___boxed(
    mut v_00_u03b1_1365_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1366_: *mut crate::leanh::LeanObject,
    mut v_inst_1367_: *mut crate::leanh::LeanObject,
    mut v_it_1368_: *mut crate::leanh::LeanObject,
    mut v_step_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1370_ = l_Std_IterM_Step_toPure(
        v_00_u03b1_1365_,
        v_00_u03b2_1366_,
        v_inst_1367_,
        v_it_1368_,
        v_step_1369_,
    );
    crate::leanh::lean_dec(v_it_1368_);
    crate::leanh::lean_dec(v_inst_1367_);
    return v_res_1370_;
}
pub unsafe fn l___private_Init_Data_Iterators_Basic_0__Std_IterStep_successor_match__1_splitter___redArg(
    mut v_x_1371_: *mut crate::leanh::LeanObject,
    mut v_h__1_1372_: *mut crate::leanh::LeanObject,
    mut v_h__2_1373_: *mut crate::leanh::LeanObject,
    mut v_h__3_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1371_) {
        0 => {
            let mut v_it_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1374_);
            crate::leanh::lean_dec(v_h__2_1373_);
            v_it_1375_ = crate::leanh::lean_ctor_get(v_x_1371_, 0);
            crate::leanh::lean_inc(v_it_1375_);
            v_out_1376_ = crate::leanh::lean_ctor_get(v_x_1371_, 1);
            crate::leanh::lean_inc(v_out_1376_);
            crate::leanh::lean_dec_ref_known(v_x_1371_, 2);
            v___x_1377_ = crate::leanh::lean_apply_2(v_h__1_1372_, v_it_1375_, v_out_1376_);
            return v___x_1377_;
        }
        1 => {
            let mut v_it_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1374_);
            crate::leanh::lean_dec(v_h__1_1372_);
            v_it_1378_ = crate::leanh::lean_ctor_get(v_x_1371_, 0);
            crate::leanh::lean_inc(v_it_1378_);
            crate::leanh::lean_dec_ref_known(v_x_1371_, 1);
            v___x_1379_ = crate::leanh::lean_apply_1(v_h__2_1373_, v_it_1378_);
            return v___x_1379_;
        }
        _ => {
            let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1373_);
            crate::leanh::lean_dec(v_h__1_1372_);
            v___x_1380_ = crate::leanh::lean_box(0);
            v___x_1381_ = crate::leanh::lean_apply_1(v_h__3_1374_, v___x_1380_);
            return v___x_1381_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Basic_0__Std_IterStep_successor_match__1_splitter(
    mut v_00_u03b1_1382_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1383_: *mut crate::leanh::LeanObject,
    mut v_motive_1384_: *mut crate::leanh::LeanObject,
    mut v_x_1385_: *mut crate::leanh::LeanObject,
    mut v_h__1_1386_: *mut crate::leanh::LeanObject,
    mut v_h__2_1387_: *mut crate::leanh::LeanObject,
    mut v_h__3_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1385_) {
        0 => {
            let mut v_it_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1388_);
            crate::leanh::lean_dec(v_h__2_1387_);
            v_it_1389_ = crate::leanh::lean_ctor_get(v_x_1385_, 0);
            crate::leanh::lean_inc(v_it_1389_);
            v_out_1390_ = crate::leanh::lean_ctor_get(v_x_1385_, 1);
            crate::leanh::lean_inc(v_out_1390_);
            crate::leanh::lean_dec_ref_known(v_x_1385_, 2);
            v___x_1391_ = crate::leanh::lean_apply_2(v_h__1_1386_, v_it_1389_, v_out_1390_);
            return v___x_1391_;
        }
        1 => {
            let mut v_it_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1388_);
            crate::leanh::lean_dec(v_h__1_1386_);
            v_it_1392_ = crate::leanh::lean_ctor_get(v_x_1385_, 0);
            crate::leanh::lean_inc(v_it_1392_);
            crate::leanh::lean_dec_ref_known(v_x_1385_, 1);
            v___x_1393_ = crate::leanh::lean_apply_1(v_h__2_1387_, v_it_1392_);
            return v___x_1393_;
        }
        _ => {
            let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1387_);
            crate::leanh::lean_dec(v_h__1_1386_);
            v___x_1394_ = crate::leanh::lean_box(0);
            v___x_1395_ = crate::leanh::lean_apply_1(v_h__3_1388_, v___x_1394_);
            return v___x_1395_;
        }
    }
}
pub unsafe fn l_Std_Iter_step___redArg(
    mut v_inst_1396_: *mut crate::leanh::LeanObject,
    mut v_it_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1403_: u8 = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut v_it_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1398_ = crate::leanh::lean_apply_1(v_inst_1396_, v_it_1397_);
                match crate::leanh::lean_obj_tag(v___x_1398_) {
                    0 => {
                        v_it_1399_ = crate::leanh::lean_ctor_get(v___x_1398_, 0);
                        v_out_1400_ = crate::leanh::lean_ctor_get(v___x_1398_, 1);
                        v_isSharedCheck_1407_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1398_)) as u8;
                        if v_isSharedCheck_1407_ == 0 {
                            v___x_1402_ = v___x_1398_;
                            v_isShared_1403_ = v_isSharedCheck_1407_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_out_1400_);
                            crate::leanh::lean_inc(v_it_1399_);
                            crate::leanh::lean_dec(v___x_1398_);
                            v___x_1402_ = crate::leanh::lean_box(0);
                            v_isShared_1403_ = v_isSharedCheck_1407_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_it_1408_ = crate::leanh::lean_ctor_get(v___x_1398_, 0);
                        v_isSharedCheck_1415_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1398_)) as u8;
                        if v_isSharedCheck_1415_ == 0 {
                            v___x_1410_ = v___x_1398_;
                            v_isShared_1411_ = v_isSharedCheck_1415_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_it_1408_);
                            crate::leanh::lean_dec(v___x_1398_);
                            v___x_1410_ = crate::leanh::lean_box(0);
                            v_isShared_1411_ = v_isSharedCheck_1415_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1416_ = crate::leanh::lean_box(2);
                        return v___x_1416_;
                    }
                }
            }
            1 => {
                if v_isShared_1403_ == 0 {
                    v___x_1405_ = v___x_1402_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_it_1399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_out_1400_);
                    v___x_1405_ = v_reuseFailAlloc_1406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1405_;
            }
            3 => {
                if v_isShared_1411_ == 0 {
                    v___x_1413_ = v___x_1410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_it_1408_);
                    v___x_1413_ = v_reuseFailAlloc_1414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iter_step(
    mut v_00_u03b1_1417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1418_: *mut crate::leanh::LeanObject,
    mut v_inst_1419_: *mut crate::leanh::LeanObject,
    mut v_it_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1426_: u8 = 0;
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1430_: u8 = 0;
    let mut v_it_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1434_: u8 = 0;
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1438_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1421_ = crate::leanh::lean_apply_1(v_inst_1419_, v_it_1420_);
                match crate::leanh::lean_obj_tag(v___x_1421_) {
                    0 => {
                        v_it_1422_ = crate::leanh::lean_ctor_get(v___x_1421_, 0);
                        v_out_1423_ = crate::leanh::lean_ctor_get(v___x_1421_, 1);
                        v_isSharedCheck_1430_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1421_)) as u8;
                        if v_isSharedCheck_1430_ == 0 {
                            v___x_1425_ = v___x_1421_;
                            v_isShared_1426_ = v_isSharedCheck_1430_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_out_1423_);
                            crate::leanh::lean_inc(v_it_1422_);
                            crate::leanh::lean_dec(v___x_1421_);
                            v___x_1425_ = crate::leanh::lean_box(0);
                            v_isShared_1426_ = v_isSharedCheck_1430_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_it_1431_ = crate::leanh::lean_ctor_get(v___x_1421_, 0);
                        v_isSharedCheck_1438_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1421_)) as u8;
                        if v_isSharedCheck_1438_ == 0 {
                            v___x_1433_ = v___x_1421_;
                            v_isShared_1434_ = v_isSharedCheck_1438_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_it_1431_);
                            crate::leanh::lean_dec(v___x_1421_);
                            v___x_1433_ = crate::leanh::lean_box(0);
                            v_isShared_1434_ = v_isSharedCheck_1438_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1439_ = crate::leanh::lean_box(2);
                        return v___x_1439_;
                    }
                }
            }
            1 => {
                if v_isShared_1426_ == 0 {
                    v___x_1428_ = v___x_1425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1429_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_it_1422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_out_1423_);
                    v___x_1428_ = v_reuseFailAlloc_1429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1428_;
            }
            3 => {
                if v_isShared_1434_ == 0 {
                    v___x_1436_ = v___x_1433_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1437_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_it_1431_);
                    v___x_1436_ = v_reuseFailAlloc_1437_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(
    mut v_00_u03b1_1440_: *mut crate::leanh::LeanObject,
    mut v_m_1441_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1442_: *mut crate::leanh::LeanObject,
    mut v_inst_1443_: *mut crate::leanh::LeanObject,
    mut v_inst_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1445_ = crate::leanh::lean_box(0);
    return v___x_1445_;
}
pub unsafe fn l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite___boxed(
    mut v_00_u03b1_1446_: *mut crate::leanh::LeanObject,
    mut v_m_1447_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1448_: *mut crate::leanh::LeanObject,
    mut v_inst_1449_: *mut crate::leanh::LeanObject,
    mut v_inst_1450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1451_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationFinite(
        v_00_u03b1_1446_,
        v_m_1447_,
        v_00_u03b2_1448_,
        v_inst_1449_,
        v_inst_1450_,
    );
    crate::leanh::lean_dec(v_inst_1449_);
    return v_res_1451_;
}
pub unsafe fn l_Std_IterM_finitelyManySteps___redArg(
    mut v_it_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1452_);
    return v_it_1452_;
}
pub unsafe fn l_Std_IterM_finitelyManySteps___redArg___boxed(
    mut v_it_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1454_ = l_Std_IterM_finitelyManySteps___redArg(v_it_1453_);
    crate::leanh::lean_dec(v_it_1453_);
    return v_res_1454_;
}
pub unsafe fn l_Std_IterM_finitelyManySteps(
    mut v_00_u03b1_1455_: *mut crate::leanh::LeanObject,
    mut v_m_1456_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1457_: *mut crate::leanh::LeanObject,
    mut v_inst_1458_: *mut crate::leanh::LeanObject,
    mut v_inst_1459_: *mut crate::leanh::LeanObject,
    mut v_it_1460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1460_);
    return v_it_1460_;
}
pub unsafe fn l_Std_IterM_finitelyManySteps___boxed(
    mut v_00_u03b1_1461_: *mut crate::leanh::LeanObject,
    mut v_m_1462_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1463_: *mut crate::leanh::LeanObject,
    mut v_inst_1464_: *mut crate::leanh::LeanObject,
    mut v_inst_1465_: *mut crate::leanh::LeanObject,
    mut v_it_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_Std_IterM_finitelyManySteps(
        v_00_u03b1_1461_,
        v_m_1462_,
        v_00_u03b2_1463_,
        v_inst_1464_,
        v_inst_1465_,
        v_it_1466_,
    );
    crate::leanh::lean_dec(v_it_1466_);
    crate::leanh::lean_dec(v_inst_1464_);
    return v_res_1467_;
}
pub unsafe fn l_Std_IterM_finitelyManySteps_x21___redArg(
    mut v_it_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1468_);
    return v_it_1468_;
}
pub unsafe fn l_Std_IterM_finitelyManySteps_x21___redArg___boxed(
    mut v_it_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Std_IterM_finitelyManySteps_x21___redArg(v_it_1469_);
    crate::leanh::lean_dec(v_it_1469_);
    return v_res_1470_;
}
pub unsafe fn l_Std_IterM_finitelyManySteps_x21(
    mut v_00_u03b1_1471_: *mut crate::leanh::LeanObject,
    mut v_m_1472_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1473_: *mut crate::leanh::LeanObject,
    mut v_inst_1474_: *mut crate::leanh::LeanObject,
    mut v_it_1475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1475_);
    return v_it_1475_;
}
pub unsafe fn l_Std_IterM_finitelyManySteps_x21___boxed(
    mut v_00_u03b1_1476_: *mut crate::leanh::LeanObject,
    mut v_m_1477_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1478_: *mut crate::leanh::LeanObject,
    mut v_inst_1479_: *mut crate::leanh::LeanObject,
    mut v_it_1480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1481_ = l_Std_IterM_finitelyManySteps_x21(
        v_00_u03b1_1476_,
        v_m_1477_,
        v_00_u03b2_1478_,
        v_inst_1479_,
        v_it_1480_,
    );
    crate::leanh::lean_dec(v_it_1480_);
    crate::leanh::lean_dec(v_inst_1479_);
    return v_res_1481_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__21;
    v___x_1528_ = l_String_toRawSubstring_x27(v___x_1527_);
    return v___x_1528_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__39;
    v___x_1565_ = l_String_toRawSubstring_x27(v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1590_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1590_;
}
pub unsafe fn l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(
    mut v_x_1591_: *mut crate::leanh::LeanObject,
    mut v_a_1592_: *mut crate::leanh::LeanObject,
    mut v_a_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u8 = 0;
    v___x_1594_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1595_ = l_Lean_Syntax_isOfKind(v_x_1591_, v___x_1594_);
    if v___x_1595_ == 0 {
        let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1596_ = crate::leanh::lean_box(1);
        v___x_1597_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1597_, 0, v___x_1596_);
        crate::leanh::lean_ctor_set(v___x_1597_, 1, v_a_1593_);
        return v___x_1597_;
    } else {
        let mut v_quotContext_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: u8 = 0;
        let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1598_ = crate::leanh::lean_ctor_get(v_a_1592_, 1);
        v_currMacroScope_1599_ = crate::leanh::lean_ctor_get(v_a_1592_, 2);
        v_ref_1600_ = crate::leanh::lean_ctor_get(v_a_1592_, 5);
        v___x_1601_ = 0;
        v___x_1602_ = l_Lean_SourceInfo_fromRef(v_ref_1600_, v___x_1601_);
        v___x_1603_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5;
        v___x_1604_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6;
        crate::leanh::lean_inc_n(v___x_1602_, 31);
        v___x_1605_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1605_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1605_, 1, v___x_1603_);
        v___x_1606_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_1607_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10;
        v___x_1608_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_1609_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1609_, 1, v___x_1608_);
        v___x_1610_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_1611_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_1612_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16;
        v___x_1613_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17;
        v___x_1614_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1614_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1614_, 1, v___x_1612_);
        v___x_1615_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20;
        v___x_1616_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__22);
        v___x_1617_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__27;
        crate::leanh::lean_inc_n(v_currMacroScope_1599_, 2);
        crate::leanh::lean_inc_n(v_quotContext_1598_, 2);
        v___x_1618_ =
            l_Lean_addMacroScope(v_quotContext_1598_, v___x_1617_, v_currMacroScope_1599_);
        v___x_1619_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__31;
        v___x_1620_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1620_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1620_, 1, v___x_1616_);
        crate::leanh::lean_ctor_set(v___x_1620_, 2, v___x_1618_);
        crate::leanh::lean_ctor_set(v___x_1620_, 3, v___x_1619_);
        v___x_1621_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33;
        v___x_1622_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34;
        v___x_1623_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1623_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1623_, 1, v___x_1622_);
        v___x_1624_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36;
        v___x_1625_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37;
        v___x_1626_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1626_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1626_, 1, v___x_1625_);
        v___x_1627_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1624_, v___x_1626_);
        v___x_1628_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38;
        v___x_1629_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1629_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1629_, 1, v___x_1628_);
        v___x_1630_ = l_Lean_Syntax_node3(
            v___x_1602_,
            v___x_1621_,
            v___x_1623_,
            v___x_1627_,
            v___x_1629_,
        );
        v___x_1631_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1606_, v___x_1630_);
        crate::leanh::lean_inc(v___x_1631_);
        v___x_1632_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1615_, v___x_1620_, v___x_1631_);
        crate::leanh::lean_inc_ref(v___x_1614_);
        v___x_1633_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1613_, v___x_1614_, v___x_1632_);
        v___x_1634_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1606_, v___x_1633_);
        v___x_1635_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1611_, v___x_1634_);
        v___x_1636_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1610_, v___x_1635_);
        crate::leanh::lean_inc_ref_n(v___x_1609_, 2);
        v___x_1637_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1607_, v___x_1609_, v___x_1636_);
        v___x_1638_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__40);
        v___x_1639_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__42;
        v___x_1640_ =
            l_Lean_addMacroScope(v_quotContext_1598_, v___x_1639_, v_currMacroScope_1599_);
        v___x_1641_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__45;
        v___x_1642_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1642_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1642_, 1, v___x_1638_);
        crate::leanh::lean_ctor_set(v___x_1642_, 2, v___x_1640_);
        crate::leanh::lean_ctor_set(v___x_1642_, 3, v___x_1641_);
        v___x_1643_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1615_, v___x_1642_, v___x_1631_);
        v___x_1644_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1613_, v___x_1614_, v___x_1643_);
        v___x_1645_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1606_, v___x_1644_);
        v___x_1646_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1611_, v___x_1645_);
        v___x_1647_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1610_, v___x_1646_);
        v___x_1648_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1607_, v___x_1609_, v___x_1647_);
        v___x_1649_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46;
        v___x_1650_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47;
        v___x_1651_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1651_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1651_, 1, v___x_1649_);
        v___x_1652_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
        v___x_1653_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1653_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1653_, 1, v___x_1606_);
        crate::leanh::lean_ctor_set(v___x_1653_, 2, v___x_1652_);
        v___x_1654_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1650_, v___x_1651_, v___x_1653_);
        v___x_1655_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1606_, v___x_1654_);
        v___x_1656_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1611_, v___x_1655_);
        v___x_1657_ = l_Lean_Syntax_node1(v___x_1602_, v___x_1610_, v___x_1656_);
        v___x_1658_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1607_, v___x_1609_, v___x_1657_);
        v___x_1659_ = l_Lean_Syntax_node3(
            v___x_1602_,
            v___x_1606_,
            v___x_1637_,
            v___x_1648_,
            v___x_1658_,
        );
        v___x_1660_ = l_Lean_Syntax_node2(v___x_1602_, v___x_1604_, v___x_1605_, v___x_1659_);
        v___x_1661_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1661_, 0, v___x_1660_);
        crate::leanh::lean_ctor_set(v___x_1661_, 1, v_a_1593_);
        return v___x_1661_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___boxed(
    mut v_x_1662_: *mut crate::leanh::LeanObject,
    mut v_a_1663_: *mut crate::leanh::LeanObject,
    mut v_a_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1665_ =
        l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1(
            v_x_1662_, v_a_1663_, v_a_1664_,
        );
    crate::leanh::lean_dec_ref(v_a_1663_);
    return v_res_1665_;
}
pub unsafe fn l_Std_Iter_finitelyManySteps___redArg(
    mut v_it_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1666_);
    return v_it_1666_;
}
pub unsafe fn l_Std_Iter_finitelyManySteps___redArg___boxed(
    mut v_it_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_Iter_finitelyManySteps___redArg(v_it_1667_);
    crate::leanh::lean_dec(v_it_1667_);
    return v_res_1668_;
}
pub unsafe fn l_Std_Iter_finitelyManySteps(
    mut v_00_u03b1_1669_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1670_: *mut crate::leanh::LeanObject,
    mut v_inst_1671_: *mut crate::leanh::LeanObject,
    mut v_inst_1672_: *mut crate::leanh::LeanObject,
    mut v_it_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1673_);
    return v_it_1673_;
}
pub unsafe fn l_Std_Iter_finitelyManySteps___boxed(
    mut v_00_u03b1_1674_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1675_: *mut crate::leanh::LeanObject,
    mut v_inst_1676_: *mut crate::leanh::LeanObject,
    mut v_inst_1677_: *mut crate::leanh::LeanObject,
    mut v_it_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1679_ = l_Std_Iter_finitelyManySteps(
        v_00_u03b1_1674_,
        v_00_u03b2_1675_,
        v_inst_1676_,
        v_inst_1677_,
        v_it_1678_,
    );
    crate::leanh::lean_dec(v_it_1678_);
    crate::leanh::lean_dec(v_inst_1676_);
    return v_res_1679_;
}
pub unsafe fn l_Std_Iter_finitelyManySteps_x21___redArg(
    mut v_it_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1680_);
    return v_it_1680_;
}
pub unsafe fn l_Std_Iter_finitelyManySteps_x21___redArg___boxed(
    mut v_it_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_Std_Iter_finitelyManySteps_x21___redArg(v_it_1681_);
    crate::leanh::lean_dec(v_it_1681_);
    return v_res_1682_;
}
pub unsafe fn l_Std_Iter_finitelyManySteps_x21(
    mut v_00_u03b1_1683_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1684_: *mut crate::leanh::LeanObject,
    mut v_inst_1685_: *mut crate::leanh::LeanObject,
    mut v_it_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1686_);
    return v_it_1686_;
}
pub unsafe fn l_Std_Iter_finitelyManySteps_x21___boxed(
    mut v_00_u03b1_1687_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1688_: *mut crate::leanh::LeanObject,
    mut v_inst_1689_: *mut crate::leanh::LeanObject,
    mut v_it_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1691_ = l_Std_Iter_finitelyManySteps_x21(
        v_00_u03b1_1687_,
        v_00_u03b2_1688_,
        v_inst_1689_,
        v_it_1690_,
    );
    crate::leanh::lean_dec(v_it_1690_);
    crate::leanh::lean_dec(v_inst_1689_);
    return v_res_1691_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1693_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__0;
    v___x_1694_ = l_String_toRawSubstring_x27(v___x_1693_);
    return v___x_1694_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__7;
    v___x_1715_ = l_String_toRawSubstring_x27(v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(
    mut v_x_1733_: *mut crate::leanh::LeanObject,
    mut v_a_1734_: *mut crate::leanh::LeanObject,
    mut v_a_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: u8 = 0;
    v___x_1736_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1737_ = l_Lean_Syntax_isOfKind(v_x_1733_, v___x_1736_);
    if v___x_1737_ == 0 {
        let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1738_ = crate::leanh::lean_box(1);
        v___x_1739_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1738_);
        crate::leanh::lean_ctor_set(v___x_1739_, 1, v_a_1735_);
        return v___x_1739_;
    } else {
        let mut v_quotContext_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1743_: u8 = 0;
        let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1740_ = crate::leanh::lean_ctor_get(v_a_1734_, 1);
        v_currMacroScope_1741_ = crate::leanh::lean_ctor_get(v_a_1734_, 2);
        v_ref_1742_ = crate::leanh::lean_ctor_get(v_a_1734_, 5);
        v___x_1743_ = 0;
        v___x_1744_ = l_Lean_SourceInfo_fromRef(v_ref_1742_, v___x_1743_);
        v___x_1745_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5;
        v___x_1746_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6;
        crate::leanh::lean_inc_n(v___x_1744_, 31);
        v___x_1747_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1747_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1747_, 1, v___x_1745_);
        v___x_1748_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_1749_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10;
        v___x_1750_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_1751_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1751_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1751_, 1, v___x_1750_);
        v___x_1752_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_1753_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_1754_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16;
        v___x_1755_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17;
        v___x_1756_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1756_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1756_, 1, v___x_1754_);
        v___x_1757_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20;
        v___x_1758_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__1);
        v___x_1759_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__3;
        crate::leanh::lean_inc_n(v_currMacroScope_1741_, 2);
        crate::leanh::lean_inc_n(v_quotContext_1740_, 2);
        v___x_1760_ =
            l_Lean_addMacroScope(v_quotContext_1740_, v___x_1759_, v_currMacroScope_1741_);
        v___x_1761_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__6;
        v___x_1762_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1762_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1762_, 1, v___x_1758_);
        crate::leanh::lean_ctor_set(v___x_1762_, 2, v___x_1760_);
        crate::leanh::lean_ctor_set(v___x_1762_, 3, v___x_1761_);
        v___x_1763_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33;
        v___x_1764_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34;
        v___x_1765_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1765_, 1, v___x_1764_);
        v___x_1766_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36;
        v___x_1767_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37;
        v___x_1768_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1768_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1768_, 1, v___x_1767_);
        v___x_1769_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1766_, v___x_1768_);
        v___x_1770_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38;
        v___x_1771_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1771_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1771_, 1, v___x_1770_);
        v___x_1772_ = l_Lean_Syntax_node3(
            v___x_1744_,
            v___x_1763_,
            v___x_1765_,
            v___x_1769_,
            v___x_1771_,
        );
        v___x_1773_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1748_, v___x_1772_);
        crate::leanh::lean_inc(v___x_1773_);
        v___x_1774_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1757_, v___x_1762_, v___x_1773_);
        crate::leanh::lean_inc_ref(v___x_1756_);
        v___x_1775_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1755_, v___x_1756_, v___x_1774_);
        v___x_1776_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1748_, v___x_1775_);
        v___x_1777_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1753_, v___x_1776_);
        v___x_1778_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1752_, v___x_1777_);
        crate::leanh::lean_inc_ref_n(v___x_1751_, 2);
        v___x_1779_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1749_, v___x_1751_, v___x_1778_);
        v___x_1780_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__8);
        v___x_1781_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__9;
        v___x_1782_ =
            l_Lean_addMacroScope(v_quotContext_1740_, v___x_1781_, v_currMacroScope_1741_);
        v___x_1783_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___closed__12;
        v___x_1784_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1784_, 1, v___x_1780_);
        crate::leanh::lean_ctor_set(v___x_1784_, 2, v___x_1782_);
        crate::leanh::lean_ctor_set(v___x_1784_, 3, v___x_1783_);
        v___x_1785_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1757_, v___x_1784_, v___x_1773_);
        v___x_1786_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1755_, v___x_1756_, v___x_1785_);
        v___x_1787_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1748_, v___x_1786_);
        v___x_1788_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1753_, v___x_1787_);
        v___x_1789_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1752_, v___x_1788_);
        v___x_1790_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1749_, v___x_1751_, v___x_1789_);
        v___x_1791_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46;
        v___x_1792_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47;
        v___x_1793_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1793_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1793_, 1, v___x_1791_);
        v___x_1794_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
        v___x_1795_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1795_, 0, v___x_1744_);
        crate::leanh::lean_ctor_set(v___x_1795_, 1, v___x_1748_);
        crate::leanh::lean_ctor_set(v___x_1795_, 2, v___x_1794_);
        v___x_1796_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1792_, v___x_1793_, v___x_1795_);
        v___x_1797_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1748_, v___x_1796_);
        v___x_1798_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1753_, v___x_1797_);
        v___x_1799_ = l_Lean_Syntax_node1(v___x_1744_, v___x_1752_, v___x_1798_);
        v___x_1800_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1749_, v___x_1751_, v___x_1799_);
        v___x_1801_ = l_Lean_Syntax_node3(
            v___x_1744_,
            v___x_1748_,
            v___x_1779_,
            v___x_1790_,
            v___x_1800_,
        );
        v___x_1802_ = l_Lean_Syntax_node2(v___x_1744_, v___x_1746_, v___x_1747_, v___x_1801_);
        v___x_1803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1803_, 0, v___x_1802_);
        crate::leanh::lean_ctor_set(v___x_1803_, 1, v_a_1735_);
        return v___x_1803_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2___boxed(
    mut v_x_1804_: *mut crate::leanh::LeanObject,
    mut v_a_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1807_ =
        l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__2(
            v_x_1804_, v_a_1805_, v_a_1806_,
        );
    crate::leanh::lean_dec_ref(v_a_1805_);
    return v_res_1807_;
}
pub unsafe fn l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(
    mut v_00_u03b1_1808_: *mut crate::leanh::LeanObject,
    mut v_m_1809_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1810_: *mut crate::leanh::LeanObject,
    mut v_inst_1811_: *mut crate::leanh::LeanObject,
    mut v_inst_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1813_ = crate::leanh::lean_box(0);
    return v___x_1813_;
}
pub unsafe fn l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive___boxed(
    mut v_00_u03b1_1814_: *mut crate::leanh::LeanObject,
    mut v_m_1815_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1816_: *mut crate::leanh::LeanObject,
    mut v_inst_1817_: *mut crate::leanh::LeanObject,
    mut v_inst_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1819_ = l_Std_IterM_TerminationMeasures_instWellFoundedRelationProductive(
        v_00_u03b1_1814_,
        v_m_1815_,
        v_00_u03b2_1816_,
        v_inst_1817_,
        v_inst_1818_,
    );
    crate::leanh::lean_dec(v_inst_1817_);
    return v_res_1819_;
}
pub unsafe fn l_Std_IterM_finitelyManySkips___redArg(
    mut v_it_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1820_);
    return v_it_1820_;
}
pub unsafe fn l_Std_IterM_finitelyManySkips___redArg___boxed(
    mut v_it_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ = l_Std_IterM_finitelyManySkips___redArg(v_it_1821_);
    crate::leanh::lean_dec(v_it_1821_);
    return v_res_1822_;
}
pub unsafe fn l_Std_IterM_finitelyManySkips(
    mut v_00_u03b1_1823_: *mut crate::leanh::LeanObject,
    mut v_m_1824_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1825_: *mut crate::leanh::LeanObject,
    mut v_inst_1826_: *mut crate::leanh::LeanObject,
    mut v_inst_1827_: *mut crate::leanh::LeanObject,
    mut v_it_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1828_);
    return v_it_1828_;
}
pub unsafe fn l_Std_IterM_finitelyManySkips___boxed(
    mut v_00_u03b1_1829_: *mut crate::leanh::LeanObject,
    mut v_m_1830_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1831_: *mut crate::leanh::LeanObject,
    mut v_inst_1832_: *mut crate::leanh::LeanObject,
    mut v_inst_1833_: *mut crate::leanh::LeanObject,
    mut v_it_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1835_ = l_Std_IterM_finitelyManySkips(
        v_00_u03b1_1829_,
        v_m_1830_,
        v_00_u03b2_1831_,
        v_inst_1832_,
        v_inst_1833_,
        v_it_1834_,
    );
    crate::leanh::lean_dec(v_it_1834_);
    crate::leanh::lean_dec(v_inst_1832_);
    return v_res_1835_;
}
pub unsafe fn l_Std_IterM_finitelyManySkips_x21___redArg(
    mut v_it_1836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1836_);
    return v_it_1836_;
}
pub unsafe fn l_Std_IterM_finitelyManySkips_x21___redArg___boxed(
    mut v_it_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Std_IterM_finitelyManySkips_x21___redArg(v_it_1837_);
    crate::leanh::lean_dec(v_it_1837_);
    return v_res_1838_;
}
pub unsafe fn l_Std_IterM_finitelyManySkips_x21(
    mut v_00_u03b1_1839_: *mut crate::leanh::LeanObject,
    mut v_m_1840_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1841_: *mut crate::leanh::LeanObject,
    mut v_inst_1842_: *mut crate::leanh::LeanObject,
    mut v_it_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1843_);
    return v_it_1843_;
}
pub unsafe fn l_Std_IterM_finitelyManySkips_x21___boxed(
    mut v_00_u03b1_1844_: *mut crate::leanh::LeanObject,
    mut v_m_1845_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1846_: *mut crate::leanh::LeanObject,
    mut v_inst_1847_: *mut crate::leanh::LeanObject,
    mut v_it_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Std_IterM_finitelyManySkips_x21(
        v_00_u03b1_1844_,
        v_m_1845_,
        v_00_u03b2_1846_,
        v_inst_1847_,
        v_it_1848_,
    );
    crate::leanh::lean_dec(v_it_1848_);
    crate::leanh::lean_dec(v_inst_1847_);
    return v_res_1849_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__0;
    v___x_1852_ = l_String_toRawSubstring_x27(v___x_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(
    mut v_x_1871_: *mut crate::leanh::LeanObject,
    mut v_a_1872_: *mut crate::leanh::LeanObject,
    mut v_a_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    v___x_1874_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1875_ = l_Lean_Syntax_isOfKind(v_x_1871_, v___x_1874_);
    if v___x_1875_ == 0 {
        let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1876_ = crate::leanh::lean_box(1);
        v___x_1877_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1877_, 0, v___x_1876_);
        crate::leanh::lean_ctor_set(v___x_1877_, 1, v_a_1873_);
        return v___x_1877_;
    } else {
        let mut v_quotContext_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1881_: u8 = 0;
        let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1878_ = crate::leanh::lean_ctor_get(v_a_1872_, 1);
        v_currMacroScope_1879_ = crate::leanh::lean_ctor_get(v_a_1872_, 2);
        v_ref_1880_ = crate::leanh::lean_ctor_get(v_a_1872_, 5);
        v___x_1881_ = 0;
        v___x_1882_ = l_Lean_SourceInfo_fromRef(v_ref_1880_, v___x_1881_);
        v___x_1883_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5;
        v___x_1884_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6;
        crate::leanh::lean_inc_n(v___x_1882_, 24);
        v___x_1885_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1885_, 0, v___x_1882_);
        crate::leanh::lean_ctor_set(v___x_1885_, 1, v___x_1883_);
        v___x_1886_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_1887_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10;
        v___x_1888_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_1889_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1889_, 0, v___x_1882_);
        crate::leanh::lean_ctor_set(v___x_1889_, 1, v___x_1888_);
        v___x_1890_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_1891_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_1892_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16;
        v___x_1893_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17;
        v___x_1894_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1894_, 0, v___x_1882_);
        crate::leanh::lean_ctor_set(v___x_1894_, 1, v___x_1892_);
        v___x_1895_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20;
        v___x_1896_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__1);
        v___x_1897_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_1879_);
        crate::leanh::lean_inc(v_quotContext_1878_);
        v___x_1898_ =
            l_Lean_addMacroScope(v_quotContext_1878_, v___x_1897_, v_currMacroScope_1879_);
        v___x_1899_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___closed__6;
        v___x_1900_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1900_, 0, v___x_1882_);
        crate::leanh::lean_ctor_set(v___x_1900_, 1, v___x_1896_);
        crate::leanh::lean_ctor_set(v___x_1900_, 2, v___x_1898_);
        crate::leanh::lean_ctor_set(v___x_1900_, 3, v___x_1899_);
        v___x_1901_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33;
        v___x_1902_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34;
        v___x_1903_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1903_, 0, v___x_1882_);
        crate::leanh::lean_ctor_set(v___x_1903_, 1, v___x_1902_);
        v___x_1904_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36;
        v___x_1905_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37;
        v___x_1906_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1906_, 0, v___x_1882_);
        crate::leanh::lean_ctor_set(v___x_1906_, 1, v___x_1905_);
        v___x_1907_ = l_Lean_Syntax_node1(v___x_1882_, v___x_1904_, v___x_1906_);
        v___x_1908_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38;
        v___x_1909_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1909_, 0, v___x_1882_);
        crate::leanh::lean_ctor_set(v___x_1909_, 1, v___x_1908_);
        v___x_1910_ = l_Lean_Syntax_node3(
            v___x_1882_,
            v___x_1901_,
            v___x_1903_,
            v___x_1907_,
            v___x_1909_,
        );
        v___x_1911_ = l_Lean_Syntax_node1(v___x_1882_, v___x_1886_, v___x_1910_);
        v___x_1912_ = l_Lean_Syntax_node2(v___x_1882_, v___x_1895_, v___x_1900_, v___x_1911_);
        v___x_1913_ = l_Lean_Syntax_node2(v___x_1882_, v___x_1893_, v___x_1894_, v___x_1912_);
        v___x_1914_ = l_Lean_Syntax_node1(v___x_1882_, v___x_1886_, v___x_1913_);
        v___x_1915_ = l_Lean_Syntax_node1(v___x_1882_, v___x_1891_, v___x_1914_);
        v___x_1916_ = l_Lean_Syntax_node1(v___x_1882_, v___x_1890_, v___x_1915_);
        crate::leanh::lean_inc_ref(v___x_1889_);
        v___x_1917_ = l_Lean_Syntax_node2(v___x_1882_, v___x_1887_, v___x_1889_, v___x_1916_);
        v___x_1918_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46;
        v___x_1919_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47;
        v___x_1920_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1920_, 0, v___x_1882_);
        crate::leanh::lean_ctor_set(v___x_1920_, 1, v___x_1918_);
        v___x_1921_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
        v___x_1922_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1922_, 0, v___x_1882_);
        crate::leanh::lean_ctor_set(v___x_1922_, 1, v___x_1886_);
        crate::leanh::lean_ctor_set(v___x_1922_, 2, v___x_1921_);
        v___x_1923_ = l_Lean_Syntax_node2(v___x_1882_, v___x_1919_, v___x_1920_, v___x_1922_);
        v___x_1924_ = l_Lean_Syntax_node1(v___x_1882_, v___x_1886_, v___x_1923_);
        v___x_1925_ = l_Lean_Syntax_node1(v___x_1882_, v___x_1891_, v___x_1924_);
        v___x_1926_ = l_Lean_Syntax_node1(v___x_1882_, v___x_1890_, v___x_1925_);
        v___x_1927_ = l_Lean_Syntax_node2(v___x_1882_, v___x_1887_, v___x_1889_, v___x_1926_);
        v___x_1928_ = l_Lean_Syntax_node2(v___x_1882_, v___x_1886_, v___x_1917_, v___x_1927_);
        v___x_1929_ = l_Lean_Syntax_node2(v___x_1882_, v___x_1884_, v___x_1885_, v___x_1928_);
        v___x_1930_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1930_, 0, v___x_1929_);
        crate::leanh::lean_ctor_set(v___x_1930_, 1, v_a_1873_);
        return v___x_1930_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3___boxed(
    mut v_x_1931_: *mut crate::leanh::LeanObject,
    mut v_a_1932_: *mut crate::leanh::LeanObject,
    mut v_a_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ =
        l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__3(
            v_x_1931_, v_a_1932_, v_a_1933_,
        );
    crate::leanh::lean_dec_ref(v_a_1932_);
    return v_res_1934_;
}
pub unsafe fn l_Std_Iter_finitelyManySkips___redArg(
    mut v_it_1935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1935_);
    return v_it_1935_;
}
pub unsafe fn l_Std_Iter_finitelyManySkips___redArg___boxed(
    mut v_it_1936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1937_ = l_Std_Iter_finitelyManySkips___redArg(v_it_1936_);
    crate::leanh::lean_dec(v_it_1936_);
    return v_res_1937_;
}
pub unsafe fn l_Std_Iter_finitelyManySkips(
    mut v_00_u03b1_1938_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1939_: *mut crate::leanh::LeanObject,
    mut v_inst_1940_: *mut crate::leanh::LeanObject,
    mut v_inst_1941_: *mut crate::leanh::LeanObject,
    mut v_it_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1942_);
    return v_it_1942_;
}
pub unsafe fn l_Std_Iter_finitelyManySkips___boxed(
    mut v_00_u03b1_1943_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1944_: *mut crate::leanh::LeanObject,
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
    mut v_inst_1946_: *mut crate::leanh::LeanObject,
    mut v_it_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1948_ = l_Std_Iter_finitelyManySkips(
        v_00_u03b1_1943_,
        v_00_u03b2_1944_,
        v_inst_1945_,
        v_inst_1946_,
        v_it_1947_,
    );
    crate::leanh::lean_dec(v_it_1947_);
    crate::leanh::lean_dec(v_inst_1945_);
    return v_res_1948_;
}
pub unsafe fn l_Std_Iter_finitelyManySkips_x21___redArg(
    mut v_it_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1949_);
    return v_it_1949_;
}
pub unsafe fn l_Std_Iter_finitelyManySkips_x21___redArg___boxed(
    mut v_it_1950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1951_ = l_Std_Iter_finitelyManySkips_x21___redArg(v_it_1950_);
    crate::leanh::lean_dec(v_it_1950_);
    return v_res_1951_;
}
pub unsafe fn l_Std_Iter_finitelyManySkips_x21(
    mut v_00_u03b1_1952_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1953_: *mut crate::leanh::LeanObject,
    mut v_inst_1954_: *mut crate::leanh::LeanObject,
    mut v_it_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_1955_);
    return v_it_1955_;
}
pub unsafe fn l_Std_Iter_finitelyManySkips_x21___boxed(
    mut v_00_u03b1_1956_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1957_: *mut crate::leanh::LeanObject,
    mut v_inst_1958_: *mut crate::leanh::LeanObject,
    mut v_it_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Std_Iter_finitelyManySkips_x21(
        v_00_u03b1_1956_,
        v_00_u03b2_1957_,
        v_inst_1958_,
        v_it_1959_,
    );
    crate::leanh::lean_dec(v_it_1959_);
    crate::leanh::lean_dec(v_inst_1958_);
    return v_res_1960_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1962_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__0;
    v___x_1963_ = l_String_toRawSubstring_x27(v___x_1962_);
    return v___x_1963_;
}
pub unsafe fn l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(
    mut v_x_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
    mut v_a_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    v___x_1984_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1985_ = l_Lean_Syntax_isOfKind(v_x_1981_, v___x_1984_);
    if v___x_1985_ == 0 {
        let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1986_ = crate::leanh::lean_box(1);
        v___x_1987_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1987_, 0, v___x_1986_);
        crate::leanh::lean_ctor_set(v___x_1987_, 1, v_a_1983_);
        return v___x_1987_;
    } else {
        let mut v_quotContext_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: u8 = 0;
        let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1988_ = crate::leanh::lean_ctor_get(v_a_1982_, 1);
        v_currMacroScope_1989_ = crate::leanh::lean_ctor_get(v_a_1982_, 2);
        v_ref_1990_ = crate::leanh::lean_ctor_get(v_a_1982_, 5);
        v___x_1991_ = 0;
        v___x_1992_ = l_Lean_SourceInfo_fromRef(v_ref_1990_, v___x_1991_);
        v___x_1993_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__5;
        v___x_1994_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__6;
        crate::leanh::lean_inc_n(v___x_1992_, 24);
        v___x_1995_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1995_, 0, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_1995_, 1, v___x_1993_);
        v___x_1996_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_1997_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__10;
        v___x_1998_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_1999_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1999_, 0, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_1999_, 1, v___x_1998_);
        v___x_2000_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_2001_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_2002_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__16;
        v___x_2003_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__17;
        v___x_2004_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2004_, 0, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_2004_, 1, v___x_2002_);
        v___x_2005_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__20;
        v___x_2006_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__1);
        v___x_2007_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_1989_);
        crate::leanh::lean_inc(v_quotContext_1988_);
        v___x_2008_ =
            l_Lean_addMacroScope(v_quotContext_1988_, v___x_2007_, v_currMacroScope_1989_);
        v___x_2009_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___closed__5;
        v___x_2010_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2010_, 0, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_2010_, 1, v___x_2006_);
        crate::leanh::lean_ctor_set(v___x_2010_, 2, v___x_2008_);
        crate::leanh::lean_ctor_set(v___x_2010_, 3, v___x_2009_);
        v___x_2011_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__33;
        v___x_2012_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__34;
        v___x_2013_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2013_, 0, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_2013_, 1, v___x_2012_);
        v___x_2014_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__36;
        v___x_2015_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__37;
        v___x_2016_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2016_, 0, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_2016_, 1, v___x_2015_);
        v___x_2017_ = l_Lean_Syntax_node1(v___x_1992_, v___x_2014_, v___x_2016_);
        v___x_2018_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__38;
        v___x_2019_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2019_, 0, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
        v___x_2020_ = l_Lean_Syntax_node3(
            v___x_1992_,
            v___x_2011_,
            v___x_2013_,
            v___x_2017_,
            v___x_2019_,
        );
        v___x_2021_ = l_Lean_Syntax_node1(v___x_1992_, v___x_1996_, v___x_2020_);
        v___x_2022_ = l_Lean_Syntax_node2(v___x_1992_, v___x_2005_, v___x_2010_, v___x_2021_);
        v___x_2023_ = l_Lean_Syntax_node2(v___x_1992_, v___x_2003_, v___x_2004_, v___x_2022_);
        v___x_2024_ = l_Lean_Syntax_node1(v___x_1992_, v___x_1996_, v___x_2023_);
        v___x_2025_ = l_Lean_Syntax_node1(v___x_1992_, v___x_2001_, v___x_2024_);
        v___x_2026_ = l_Lean_Syntax_node1(v___x_1992_, v___x_2000_, v___x_2025_);
        crate::leanh::lean_inc_ref(v___x_1999_);
        v___x_2027_ = l_Lean_Syntax_node2(v___x_1992_, v___x_1997_, v___x_1999_, v___x_2026_);
        v___x_2028_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__46;
        v___x_2029_ = l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__47;
        v___x_2030_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2030_, 0, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_2030_, 1, v___x_2028_);
        v___x_2031_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48_once), _init_l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__1___closed__48);
        v___x_2032_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2032_, 0, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_2032_, 1, v___x_1996_);
        crate::leanh::lean_ctor_set(v___x_2032_, 2, v___x_2031_);
        v___x_2033_ = l_Lean_Syntax_node2(v___x_1992_, v___x_2029_, v___x_2030_, v___x_2032_);
        v___x_2034_ = l_Lean_Syntax_node1(v___x_1992_, v___x_1996_, v___x_2033_);
        v___x_2035_ = l_Lean_Syntax_node1(v___x_1992_, v___x_2001_, v___x_2034_);
        v___x_2036_ = l_Lean_Syntax_node1(v___x_1992_, v___x_2000_, v___x_2035_);
        v___x_2037_ = l_Lean_Syntax_node2(v___x_1992_, v___x_1997_, v___x_1999_, v___x_2036_);
        v___x_2038_ = l_Lean_Syntax_node2(v___x_1992_, v___x_1996_, v___x_2027_, v___x_2037_);
        v___x_2039_ = l_Lean_Syntax_node2(v___x_1992_, v___x_1994_, v___x_1995_, v___x_2038_);
        v___x_2040_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2040_, 0, v___x_2039_);
        crate::leanh::lean_ctor_set(v___x_2040_, 1, v_a_1983_);
        return v___x_2040_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4___boxed(
    mut v_x_2041_: *mut crate::leanh::LeanObject,
    mut v_a_2042_: *mut crate::leanh::LeanObject,
    mut v_a_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2044_ =
        l_Std___aux__Init__Data__Iterators__Basic______macroRules__tacticDecreasing__trivial__4(
            v_x_2041_, v_a_2042_, v_a_2043_,
        );
    crate::leanh::lean_dec_ref(v_a_2042_);
    return v_res_2044_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Basic(builtin);
}
