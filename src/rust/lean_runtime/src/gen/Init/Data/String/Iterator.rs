// Lean compiler output
// Module: Init.Data.String.Iterator
// Imports: Init.Data.String.Modify
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_String_toRawSubstring_x27,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_get_fast,
    lean_string_utf8_next, lean_string_utf8_next_fast, lean_string_utf8_prev,
};
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
    lean_string_utf8_byte_size,
};
pub static l_String_Legacy_instInhabitedIterator_default___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_String_Legacy_instInhabitedIterator_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_instInhabitedIterator_default___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_String_Legacy_instInhabitedIterator_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Legacy_instInhabitedIterator_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Legacy_instInhabitedIterator: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_instSizeOfIterator___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_Legacy_instSizeOfIterator___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_Legacy_instSizeOfIterator___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instSizeOfIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Legacy_instSizeOfIterator: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instSizeOfIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114, 105, 118, 105, 97, 108, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut crate::leanh::LeanObject,5744670087858236374 as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut crate::leanh::LeanObject,6022092293134036165 as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut crate::leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut crate::leanh::LeanObject,5826123769708379594 as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16_value: crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [83, 116, 114, 105, 110, 103, 46, 76, 101, 103, 97, 99, 121, 46, 73, 116, 101, 114, 97, 116, 111, 114, 46, 115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 104, 97, 115, 78, 101, 120, 116, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 105, 110, 103, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 101, 103, 97, 99, 121, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 116, 101, 114, 97, 116, 111, 114, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 104, 97, 115, 78, 101, 120, 116, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value) as *mut crate::leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut crate::leanh::LeanObject,16221383843924677366 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut crate::leanh::LeanObject,13785796134284214332 as *mut crate::leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value) as *mut crate::leanh::LeanObject,17921308319265575761 as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut crate::leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut crate::leanh::LeanObject,16687334436616221424 as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0_value: crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [83, 116, 114, 105, 110, 103, 46, 76, 101, 103, 97, 99, 121, 46, 73, 116, 101, 114, 97, 116, 111, 114, 46, 115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 97, 116, 69, 110, 100, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 97, 116, 69, 110, 100, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut crate::leanh::LeanObject,16221383843924677366 as *mut crate::leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut crate::leanh::LeanObject,13785796134284214332 as *mut crate::leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,4155438117962710745 as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__0_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            83, 116, 114, 105, 110, 103, 46, 73, 116, 101, 114, 97, 116, 111, 114, 46, 109, 107,
            32, 0,
        ],
    };
static mut l_instReprIterator___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprIterator___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprIterator___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [32, 0],
    };
static mut l_instReprIterator___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprIterator___lam__0___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprIterator___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__4_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [123, 32, 98, 121, 116, 101, 73, 100, 120, 32, 58, 61, 32, 0],
    };
static mut l_instReprIterator___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprIterator___lam__0___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprIterator___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__6_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [32, 125, 0],
    };
static mut l_instReprIterator___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprIterator___lam__0___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprIterator___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprIterator___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instReprIterator___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprIterator___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprIterator: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringIterator___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringIterator___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringIterator___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringIterator___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringIterator: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringIterator___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_String_Legacy_instDecidableEqIterator_decEq(
    mut v_x_582_: *mut crate::leanh::LeanObject,
    mut v_x_583_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_s_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    v_s_584_ = crate::leanh::lean_ctor_get(v_x_582_, 0);
    v_i_585_ = crate::leanh::lean_ctor_get(v_x_582_, 1);
    v_s_586_ = crate::leanh::lean_ctor_get(v_x_583_, 0);
    v_i_587_ = crate::leanh::lean_ctor_get(v_x_583_, 1);
    v___x_588_ = lean_string_dec_eq(v_s_584_, v_s_586_);
    if v___x_588_ == 0 {
        return v___x_588_;
    } else {
        let mut v___x_589_: u8 = 0;
        v___x_589_ = lean_nat_dec_eq(v_i_585_, v_i_587_);
        return v___x_589_;
    }
}
pub unsafe fn l_String_Legacy_instDecidableEqIterator_decEq___boxed(
    mut v_x_590_: *mut crate::leanh::LeanObject,
    mut v_x_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_592_: u8 = 0;
    let mut v_r_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_592_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_590_, v_x_591_);
    crate::leanh::lean_dec_ref(v_x_591_);
    crate::leanh::lean_dec_ref(v_x_590_);
    v_r_593_ = crate::leanh::lean_box((v_res_592_) as usize);
    return v_r_593_;
}
pub unsafe fn l_String_Legacy_instDecidableEqIterator(
    mut v_x_594_: *mut crate::leanh::LeanObject,
    mut v_x_595_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_596_: u8 = 0;
    v___x_596_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_594_, v_x_595_);
    return v___x_596_;
}
pub unsafe fn l_String_Legacy_instDecidableEqIterator___boxed(
    mut v_x_597_: *mut crate::leanh::LeanObject,
    mut v_x_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_599_: u8 = 0;
    let mut v_r_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_599_ = l_String_Legacy_instDecidableEqIterator(v_x_597_, v_x_598_);
    crate::leanh::lean_dec_ref(v_x_598_);
    crate::leanh::lean_dec_ref(v_x_597_);
    v_r_600_ = crate::leanh::lean_box((v_res_599_) as usize);
    return v_r_600_;
}
pub unsafe fn l_String_Legacy_mkIterator(
    mut v_s_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_609_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_609_, 0, v_s_607_);
    crate::leanh::lean_ctor_set(v___x_609_, 1, v___x_608_);
    return v___x_609_;
}
pub unsafe fn l_String_Legacy_iter(
    mut v_s_610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_611_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_612_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_612_, 0, v_s_610_);
    crate::leanh::lean_ctor_set(v___x_612_, 1, v___x_611_);
    return v___x_612_;
}
pub unsafe fn l_String_Legacy_instSizeOfIterator___lam__0(
    mut v_i_613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_614_ = crate::leanh::lean_ctor_get(v_i_613_, 0);
    v_i_615_ = crate::leanh::lean_ctor_get(v_i_613_, 1);
    v___x_616_ = lean_string_utf8_byte_size(v_s_614_);
    v___x_617_ = lean_nat_sub(v___x_616_, v_i_615_);
    return v___x_617_;
}
pub unsafe fn l_String_Legacy_instSizeOfIterator___lam__0___boxed(
    mut v_i_618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_619_ = l_String_Legacy_instSizeOfIterator___lam__0(v_i_618_);
    crate::leanh::lean_dec_ref(v_i_618_);
    return v_res_619_;
}
pub unsafe fn l_String_Legacy_Iterator_toString(
    mut v_self_622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_623_ = crate::leanh::lean_ctor_get(v_self_622_, 0);
    crate::leanh::lean_inc_ref(v_s_623_);
    return v_s_623_;
}
pub unsafe fn l_String_Legacy_Iterator_toString___boxed(
    mut v_self_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_625_ = l_String_Legacy_Iterator_toString(v_self_624_);
    crate::leanh::lean_dec_ref(v_self_624_);
    return v_res_625_;
}
pub unsafe fn l_String_Legacy_Iterator_remainingBytes(
    mut v_x_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_627_ = crate::leanh::lean_ctor_get(v_x_626_, 0);
    v_i_628_ = crate::leanh::lean_ctor_get(v_x_626_, 1);
    v___x_629_ = lean_string_utf8_byte_size(v_s_627_);
    v___x_630_ = lean_nat_sub(v___x_629_, v_i_628_);
    return v___x_630_;
}
pub unsafe fn l_String_Legacy_Iterator_remainingBytes___boxed(
    mut v_x_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_632_ = l_String_Legacy_Iterator_remainingBytes(v_x_631_);
    crate::leanh::lean_dec_ref(v_x_631_);
    return v_res_632_;
}
pub unsafe fn l_String_Legacy_Iterator_pos(
    mut v_self_633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_634_ = crate::leanh::lean_ctor_get(v_self_633_, 1);
    crate::leanh::lean_inc(v_i_634_);
    return v_i_634_;
}
pub unsafe fn l_String_Legacy_Iterator_pos___boxed(
    mut v_self_635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_636_ = l_String_Legacy_Iterator_pos(v_self_635_);
    crate::leanh::lean_dec_ref(v_self_635_);
    return v_res_636_;
}
pub unsafe fn l_String_Legacy_Iterator_curr(mut v_x_637_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v_s_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: u32 = 0;
    v_s_638_ = crate::leanh::lean_ctor_get(v_x_637_, 0);
    v_i_639_ = crate::leanh::lean_ctor_get(v_x_637_, 1);
    v___x_640_ = lean_string_utf8_get(v_s_638_, v_i_639_);
    return v___x_640_;
}
pub unsafe fn l_String_Legacy_Iterator_curr___boxed(
    mut v_x_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_642_: u32 = 0;
    let mut v_r_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ = l_String_Legacy_Iterator_curr(v_x_641_);
    crate::leanh::lean_dec_ref(v_x_641_);
    v_r_643_ = crate::leanh::lean_box_uint32(v_res_642_);
    return v_r_643_;
}
pub unsafe fn l_String_Legacy_Iterator_next(
    mut v_x_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_645_ = crate::leanh::lean_ctor_get(v_x_644_, 0);
                v_i_646_ = crate::leanh::lean_ctor_get(v_x_644_, 1);
                v_isSharedCheck_654_ = (!crate::leanh::lean_is_exclusive(v_x_644_)) as u8;
                if v_isSharedCheck_654_ == 0 {
                    v___x_648_ = v_x_644_;
                    v_isShared_649_ = v_isSharedCheck_654_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_i_646_);
                    crate::leanh::lean_inc(v_s_645_);
                    crate::leanh::lean_dec(v_x_644_);
                    v___x_648_ = crate::leanh::lean_box(0);
                    v_isShared_649_ = v_isSharedCheck_654_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_650_ = lean_string_utf8_next(v_s_645_, v_i_646_);
                crate::leanh::lean_dec(v_i_646_);
                if v_isShared_649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_648_, 1, v___x_650_);
                    v___x_652_ = v___x_648_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v_s_645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
                    v___x_652_ = v_reuseFailAlloc_653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_prev(
    mut v_x_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_656_ = crate::leanh::lean_ctor_get(v_x_655_, 0);
                v_i_657_ = crate::leanh::lean_ctor_get(v_x_655_, 1);
                v_isSharedCheck_665_ = (!crate::leanh::lean_is_exclusive(v_x_655_)) as u8;
                if v_isSharedCheck_665_ == 0 {
                    v___x_659_ = v_x_655_;
                    v_isShared_660_ = v_isSharedCheck_665_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_i_657_);
                    crate::leanh::lean_inc(v_s_656_);
                    crate::leanh::lean_dec(v_x_655_);
                    v___x_659_ = crate::leanh::lean_box(0);
                    v_isShared_660_ = v_isSharedCheck_665_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_661_ = lean_string_utf8_prev(v_s_656_, v_i_657_);
                crate::leanh::lean_dec(v_i_657_);
                if v_isShared_660_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_659_, 1, v___x_661_);
                    v___x_663_ = v___x_659_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 0, v_s_656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
                    v___x_663_ = v_reuseFailAlloc_664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_atEnd(mut v_x_666_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_s_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: u8 = 0;
    v_s_667_ = crate::leanh::lean_ctor_get(v_x_666_, 0);
    v_i_668_ = crate::leanh::lean_ctor_get(v_x_666_, 1);
    v___x_669_ = lean_string_utf8_byte_size(v_s_667_);
    v___x_670_ = lean_nat_dec_le(v___x_669_, v_i_668_);
    return v___x_670_;
}
pub unsafe fn l_String_Legacy_Iterator_atEnd___boxed(
    mut v_x_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_672_: u8 = 0;
    let mut v_r_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_672_ = l_String_Legacy_Iterator_atEnd(v_x_671_);
    crate::leanh::lean_dec_ref(v_x_671_);
    v_r_673_ = crate::leanh::lean_box((v_res_672_) as usize);
    return v_r_673_;
}
pub unsafe fn l_String_Legacy_Iterator_hasNext(mut v_x_674_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_s_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u8 = 0;
    v_s_675_ = crate::leanh::lean_ctor_get(v_x_674_, 0);
    v_i_676_ = crate::leanh::lean_ctor_get(v_x_674_, 1);
    v___x_677_ = lean_string_utf8_byte_size(v_s_675_);
    v___x_678_ = lean_nat_dec_lt(v_i_676_, v___x_677_);
    return v___x_678_;
}
pub unsafe fn l_String_Legacy_Iterator_hasNext___boxed(
    mut v_x_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_680_: u8 = 0;
    let mut v_r_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_680_ = l_String_Legacy_Iterator_hasNext(v_x_679_);
    crate::leanh::lean_dec_ref(v_x_679_);
    v_r_681_ = crate::leanh::lean_box((v_res_680_) as usize);
    return v_r_681_;
}
pub unsafe fn l_String_Legacy_Iterator_hasPrev(mut v_x_682_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_i_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    v_i_683_ = crate::leanh::lean_ctor_get(v_x_682_, 1);
    v___x_684_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_685_ = lean_nat_dec_lt(v___x_684_, v_i_683_);
    return v___x_685_;
}
pub unsafe fn l_String_Legacy_Iterator_hasPrev___boxed(
    mut v_x_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_687_: u8 = 0;
    let mut v_r_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_687_ = l_String_Legacy_Iterator_hasPrev(v_x_686_);
    crate::leanh::lean_dec_ref(v_x_686_);
    v_r_688_ = crate::leanh::lean_box((v_res_687_) as usize);
    return v_r_688_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter___redArg(
    mut v_x_689_: *mut crate::leanh::LeanObject,
    mut v_h__1_690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_691_ = crate::leanh::lean_ctor_get(v_x_689_, 0);
    crate::leanh::lean_inc_ref(v_s_691_);
    v_i_692_ = crate::leanh::lean_ctor_get(v_x_689_, 1);
    crate::leanh::lean_inc(v_i_692_);
    crate::leanh::lean_dec_ref(v_x_689_);
    v___x_693_ = crate::leanh::lean_apply_2(v_h__1_690_, v_s_691_, v_i_692_);
    return v___x_693_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter(
    mut v_motive_694_: *mut crate::leanh::LeanObject,
    mut v_x_695_: *mut crate::leanh::LeanObject,
    mut v_h__1_696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_697_ = crate::leanh::lean_ctor_get(v_x_695_, 0);
    crate::leanh::lean_inc_ref(v_s_697_);
    v_i_698_ = crate::leanh::lean_ctor_get(v_x_695_, 1);
    crate::leanh::lean_inc(v_i_698_);
    crate::leanh::lean_dec_ref(v_x_695_);
    v___x_699_ = crate::leanh::lean_apply_2(v_h__1_696_, v_s_697_, v_i_698_);
    return v___x_699_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(
    mut v_x_700_: *mut crate::leanh::LeanObject,
    mut v_x_701_: *mut crate::leanh::LeanObject,
    mut v_h__1_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = crate::leanh::lean_apply_2(v_h__1_702_, v_x_700_, v_x_701_);
    return v___x_703_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter(
    mut v_motive_704_: *mut crate::leanh::LeanObject,
    mut v_x_705_: *mut crate::leanh::LeanObject,
    mut v_x_706_: *mut crate::leanh::LeanObject,
    mut v_h__1_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = crate::leanh::lean_apply_2(v_h__1_707_, v_x_705_, v_x_706_);
    return v___x_708_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27___redArg(
    mut v_it_709_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v_s_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u32 = 0;
    v_s_710_ = crate::leanh::lean_ctor_get(v_it_709_, 0);
    v_i_711_ = crate::leanh::lean_ctor_get(v_it_709_, 1);
    v___x_712_ = lean_string_utf8_get_fast(v_s_710_, v_i_711_);
    return v___x_712_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27___redArg___boxed(
    mut v_it_713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_714_: u32 = 0;
    let mut v_r_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_714_ = l_String_Legacy_Iterator_curr_x27___redArg(v_it_713_);
    crate::leanh::lean_dec_ref(v_it_713_);
    v_r_715_ = crate::leanh::lean_box_uint32(v_res_714_);
    return v_r_715_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27(
    mut v_it_716_: *mut crate::leanh::LeanObject,
    mut v_h_717_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v_s_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u32 = 0;
    v_s_718_ = crate::leanh::lean_ctor_get(v_it_716_, 0);
    v_i_719_ = crate::leanh::lean_ctor_get(v_it_716_, 1);
    v___x_720_ = lean_string_utf8_get_fast(v_s_718_, v_i_719_);
    return v___x_720_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27___boxed(
    mut v_it_721_: *mut crate::leanh::LeanObject,
    mut v_h_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_723_: u32 = 0;
    let mut v_r_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ = l_String_Legacy_Iterator_curr_x27(v_it_721_, v_h_722_);
    crate::leanh::lean_dec_ref(v_it_721_);
    v_r_724_ = crate::leanh::lean_box_uint32(v_res_723_);
    return v_r_724_;
}
pub unsafe fn l_String_Legacy_Iterator_next_x27___redArg(
    mut v_it_725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_726_ = crate::leanh::lean_ctor_get(v_it_725_, 0);
                v_i_727_ = crate::leanh::lean_ctor_get(v_it_725_, 1);
                v_isSharedCheck_735_ = (!crate::leanh::lean_is_exclusive(v_it_725_)) as u8;
                if v_isSharedCheck_735_ == 0 {
                    v___x_729_ = v_it_725_;
                    v_isShared_730_ = v_isSharedCheck_735_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_i_727_);
                    crate::leanh::lean_inc(v_s_726_);
                    crate::leanh::lean_dec(v_it_725_);
                    v___x_729_ = crate::leanh::lean_box(0);
                    v_isShared_730_ = v_isSharedCheck_735_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_731_ = lean_string_utf8_next_fast(v_s_726_, v_i_727_);
                crate::leanh::lean_dec(v_i_727_);
                if v_isShared_730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_729_, 1, v___x_731_);
                    v___x_733_ = v___x_729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_734_, 0, v_s_726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_731_);
                    v___x_733_ = v_reuseFailAlloc_734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_next_x27(
    mut v_it_736_: *mut crate::leanh::LeanObject,
    mut v_h_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_738_ = crate::leanh::lean_ctor_get(v_it_736_, 0);
                v_i_739_ = crate::leanh::lean_ctor_get(v_it_736_, 1);
                v_isSharedCheck_747_ = (!crate::leanh::lean_is_exclusive(v_it_736_)) as u8;
                if v_isSharedCheck_747_ == 0 {
                    v___x_741_ = v_it_736_;
                    v_isShared_742_ = v_isSharedCheck_747_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_i_739_);
                    crate::leanh::lean_inc(v_s_738_);
                    crate::leanh::lean_dec(v_it_736_);
                    v___x_741_ = crate::leanh::lean_box(0);
                    v_isShared_742_ = v_isSharedCheck_747_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_743_ = lean_string_utf8_next_fast(v_s_738_, v_i_739_);
                crate::leanh::lean_dec(v_i_739_);
                if v_isShared_742_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_741_, 1, v___x_743_);
                    v___x_745_ = v___x_741_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_746_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 0, v_s_738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_743_);
                    v___x_745_ = v_reuseFailAlloc_746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_toEnd(
    mut v_x_748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_752_: u8 = 0;
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_757_: u8 = 0;
    let mut v_unused_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_749_ = crate::leanh::lean_ctor_get(v_x_748_, 0);
                v_isSharedCheck_757_ = (!crate::leanh::lean_is_exclusive(v_x_748_)) as u8;
                if v_isSharedCheck_757_ == 0 {
                    v_unused_758_ = crate::leanh::lean_ctor_get(v_x_748_, 1);
                    crate::leanh::lean_dec(v_unused_758_);
                    v___x_751_ = v_x_748_;
                    v_isShared_752_ = v_isSharedCheck_757_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_s_749_);
                    crate::leanh::lean_dec(v_x_748_);
                    v___x_751_ = crate::leanh::lean_box(0);
                    v_isShared_752_ = v_isSharedCheck_757_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_753_ = lean_string_utf8_byte_size(v_s_749_);
                if v_isShared_752_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_751_, 1, v___x_753_);
                    v___x_755_ = v___x_751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_756_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_756_, 0, v_s_749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
                    v___x_755_ = v_reuseFailAlloc_756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_extract(
    mut v_x_759_: *mut crate::leanh::LeanObject,
    mut v_x_760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: u8 = 0;
    v_s_761_ = crate::leanh::lean_ctor_get(v_x_759_, 0);
    v_i_762_ = crate::leanh::lean_ctor_get(v_x_759_, 1);
    v_s_763_ = crate::leanh::lean_ctor_get(v_x_760_, 0);
    v_i_764_ = crate::leanh::lean_ctor_get(v_x_760_, 1);
    v___x_765_ = lean_string_dec_eq(v_s_761_, v_s_763_);
    if v___x_765_ == 0 {
        let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_766_ = l_String_Legacy_instInhabitedIterator_default___closed__0;
        return v___x_766_;
    } else {
        let mut v___x_767_: u8 = 0;
        v___x_767_ = lean_nat_dec_lt(v_i_764_, v_i_762_);
        if v___x_767_ == 0 {
            let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_768_ = lean_string_utf8_extract(v_s_761_, v_i_762_, v_i_764_);
            return v___x_768_;
        } else {
            let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_769_ = l_String_Legacy_instInhabitedIterator_default___closed__0;
            return v___x_769_;
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_extract___boxed(
    mut v_x_770_: *mut crate::leanh::LeanObject,
    mut v_x_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_772_ = l_String_Legacy_Iterator_extract(v_x_770_, v_x_771_);
    crate::leanh::lean_dec_ref(v_x_771_);
    crate::leanh::lean_dec_ref(v_x_770_);
    return v_res_772_;
}
pub unsafe fn l_String_Legacy_Iterator_forward(
    mut v_x_773_: *mut crate::leanh::LeanObject,
    mut v_x_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_776_: u8 = 0;
    let mut v_s_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_781_: u8 = 0;
    let mut v_one_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_775_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_776_ = lean_nat_dec_eq(v_x_774_, v_zero_775_);
                if v_isZero_776_ == 1 {
                    crate::leanh::lean_dec(v_x_774_);
                    return v_x_773_;
                } else {
                    v_s_777_ = crate::leanh::lean_ctor_get(v_x_773_, 0);
                    v_i_778_ = crate::leanh::lean_ctor_get(v_x_773_, 1);
                    v_isSharedCheck_789_ = (!crate::leanh::lean_is_exclusive(v_x_773_)) as u8;
                    if v_isSharedCheck_789_ == 0 {
                        v___x_780_ = v_x_773_;
                        v_isShared_781_ = v_isSharedCheck_789_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_i_778_);
                        crate::leanh::lean_inc(v_s_777_);
                        crate::leanh::lean_dec(v_x_773_);
                        v___x_780_ = crate::leanh::lean_box(0);
                        v_isShared_781_ = v_isSharedCheck_789_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_782_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_783_ = lean_nat_sub(v_x_774_, v_one_782_);
                crate::leanh::lean_dec(v_x_774_);
                v___x_784_ = lean_string_utf8_next(v_s_777_, v_i_778_);
                crate::leanh::lean_dec(v_i_778_);
                if v_isShared_781_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_780_, 1, v___x_784_);
                    v___x_786_ = v___x_780_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 0, v_s_777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_784_);
                    v___x_786_ = v_reuseFailAlloc_788_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_773_ = v___x_786_;
                v_x_774_ = v_n_783_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_remainingToString(
    mut v_x_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_791_ = crate::leanh::lean_ctor_get(v_x_790_, 0);
    v_i_792_ = crate::leanh::lean_ctor_get(v_x_790_, 1);
    v___x_793_ = lean_string_utf8_byte_size(v_s_791_);
    v___x_794_ = lean_string_utf8_extract(v_s_791_, v_i_792_, v___x_793_);
    return v___x_794_;
}
pub unsafe fn l_String_Legacy_Iterator_remainingToString___boxed(
    mut v_x_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_796_ = l_String_Legacy_Iterator_remainingToString(v_x_795_);
    crate::leanh::lean_dec_ref(v_x_795_);
    return v_res_796_;
}
pub unsafe fn l_String_Legacy_Iterator_nextn(
    mut v_x_797_: *mut crate::leanh::LeanObject,
    mut v_x_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_800_: u8 = 0;
    let mut v_s_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v_one_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_799_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_800_ = lean_nat_dec_eq(v_x_798_, v_zero_799_);
                if v_isZero_800_ == 1 {
                    crate::leanh::lean_dec(v_x_798_);
                    return v_x_797_;
                } else {
                    v_s_801_ = crate::leanh::lean_ctor_get(v_x_797_, 0);
                    v_i_802_ = crate::leanh::lean_ctor_get(v_x_797_, 1);
                    v_isSharedCheck_813_ = (!crate::leanh::lean_is_exclusive(v_x_797_)) as u8;
                    if v_isSharedCheck_813_ == 0 {
                        v___x_804_ = v_x_797_;
                        v_isShared_805_ = v_isSharedCheck_813_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_i_802_);
                        crate::leanh::lean_inc(v_s_801_);
                        crate::leanh::lean_dec(v_x_797_);
                        v___x_804_ = crate::leanh::lean_box(0);
                        v_isShared_805_ = v_isSharedCheck_813_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_806_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_807_ = lean_nat_sub(v_x_798_, v_one_806_);
                crate::leanh::lean_dec(v_x_798_);
                v___x_808_ = lean_string_utf8_next(v_s_801_, v_i_802_);
                crate::leanh::lean_dec(v_i_802_);
                if v_isShared_805_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_804_, 1, v___x_808_);
                    v___x_810_ = v___x_804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_812_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 0, v_s_801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_808_);
                    v___x_810_ = v_reuseFailAlloc_812_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_797_ = v___x_810_;
                v_x_798_ = v_n_807_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_prevn(
    mut v_x_814_: *mut crate::leanh::LeanObject,
    mut v_x_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_817_: u8 = 0;
    let mut v_s_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v_one_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_816_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_817_ = lean_nat_dec_eq(v_x_815_, v_zero_816_);
                if v_isZero_817_ == 1 {
                    crate::leanh::lean_dec(v_x_815_);
                    return v_x_814_;
                } else {
                    v_s_818_ = crate::leanh::lean_ctor_get(v_x_814_, 0);
                    v_i_819_ = crate::leanh::lean_ctor_get(v_x_814_, 1);
                    v_isSharedCheck_830_ = (!crate::leanh::lean_is_exclusive(v_x_814_)) as u8;
                    if v_isSharedCheck_830_ == 0 {
                        v___x_821_ = v_x_814_;
                        v_isShared_822_ = v_isSharedCheck_830_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_i_819_);
                        crate::leanh::lean_inc(v_s_818_);
                        crate::leanh::lean_dec(v_x_814_);
                        v___x_821_ = crate::leanh::lean_box(0);
                        v_isShared_822_ = v_isSharedCheck_830_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_823_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_824_ = lean_nat_sub(v_x_815_, v_one_823_);
                crate::leanh::lean_dec(v_x_815_);
                v___x_825_ = lean_string_utf8_prev(v_s_818_, v_i_819_);
                crate::leanh::lean_dec(v_i_819_);
                if v_isShared_822_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_821_, 1, v___x_825_);
                    v___x_827_ = v___x_821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_829_, 0, v_s_818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_825_);
                    v___x_827_ = v_reuseFailAlloc_829_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_814_ = v___x_827_;
                v_x_815_ = v_n_824_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16;
    v___x_867_ = l_String_toRawSubstring_x27(v___x_866_);
    return v___x_867_;
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(
    mut v_x_890_: *mut crate::leanh::LeanObject,
    mut v_a_891_: *mut crate::leanh::LeanObject,
    mut v_a_892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: u8 = 0;
    v___x_893_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_894_ = l_Lean_Syntax_isOfKind(v_x_890_, v___x_893_);
    if v___x_894_ == 0 {
        let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_895_ = crate::leanh::lean_box(1);
        v___x_896_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_895_);
        crate::leanh::lean_ctor_set(v___x_896_, 1, v_a_892_);
        return v___x_896_;
    } else {
        let mut v_quotContext_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_900_: u8 = 0;
        let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_897_ = crate::leanh::lean_ctor_get(v_a_891_, 1);
        v_currMacroScope_898_ = crate::leanh::lean_ctor_get(v_a_891_, 2);
        v_ref_899_ = crate::leanh::lean_ctor_get(v_a_891_, 5);
        v___x_900_ = 0;
        v___x_901_ = l_Lean_SourceInfo_fromRef(v_ref_899_, v___x_900_);
        v___x_902_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_903_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7;
        crate::leanh::lean_inc_n(v___x_901_, 10);
        v___x_904_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_904_, 0, v___x_901_);
        crate::leanh::lean_ctor_set(v___x_904_, 1, v___x_903_);
        v___x_905_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9;
        v___x_906_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_907_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_908_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14;
        v___x_909_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_910_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_910_, 0, v___x_901_);
        crate::leanh::lean_ctor_set(v___x_910_, 1, v___x_908_);
        v___x_911_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17), core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once), _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17);
        v___x_912_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22;
        crate::leanh::lean_inc(v_currMacroScope_898_);
        crate::leanh::lean_inc(v_quotContext_897_);
        v___x_913_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_912_, v_currMacroScope_898_);
        v___x_914_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24;
        v___x_915_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_915_, 0, v___x_901_);
        crate::leanh::lean_ctor_set(v___x_915_, 1, v___x_911_);
        crate::leanh::lean_ctor_set(v___x_915_, 2, v___x_913_);
        crate::leanh::lean_ctor_set(v___x_915_, 3, v___x_914_);
        v___x_916_ = l_Lean_Syntax_node2(v___x_901_, v___x_909_, v___x_910_, v___x_915_);
        v___x_917_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_918_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_918_, 0, v___x_901_);
        crate::leanh::lean_ctor_set(v___x_918_, 1, v___x_917_);
        v___x_919_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26;
        v___x_920_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_921_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_921_, 0, v___x_901_);
        crate::leanh::lean_ctor_set(v___x_921_, 1, v___x_919_);
        v___x_922_ = l_Lean_Syntax_node1(v___x_901_, v___x_920_, v___x_921_);
        v___x_923_ =
            l_Lean_Syntax_node3(v___x_901_, v___x_907_, v___x_916_, v___x_918_, v___x_922_);
        v___x_924_ = l_Lean_Syntax_node1(v___x_901_, v___x_906_, v___x_923_);
        v___x_925_ = l_Lean_Syntax_node1(v___x_901_, v___x_905_, v___x_924_);
        v___x_926_ = l_Lean_Syntax_node2(v___x_901_, v___x_902_, v___x_904_, v___x_925_);
        v___x_927_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_927_, 0, v___x_926_);
        crate::leanh::lean_ctor_set(v___x_927_, 1, v_a_892_);
        return v___x_927_;
    }
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___boxed(
    mut v_x_928_: *mut crate::leanh::LeanObject,
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(v_x_928_, v_a_929_, v_a_930_);
    crate::leanh::lean_dec_ref(v_a_929_);
    return v_res_931_;
}
pub unsafe fn _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0;
    v___x_934_ = l_String_toRawSubstring_x27(v___x_933_);
    return v___x_934_;
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(
    mut v_x_947_: *mut crate::leanh::LeanObject,
    mut v_a_948_: *mut crate::leanh::LeanObject,
    mut v_a_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: u8 = 0;
    v___x_950_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_951_ = l_Lean_Syntax_isOfKind(v_x_947_, v___x_950_);
    if v___x_951_ == 0 {
        let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_952_ = crate::leanh::lean_box(1);
        v___x_953_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_953_, 0, v___x_952_);
        crate::leanh::lean_ctor_set(v___x_953_, 1, v_a_949_);
        return v___x_953_;
    } else {
        let mut v_quotContext_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_957_: u8 = 0;
        let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_954_ = crate::leanh::lean_ctor_get(v_a_948_, 1);
        v_currMacroScope_955_ = crate::leanh::lean_ctor_get(v_a_948_, 2);
        v_ref_956_ = crate::leanh::lean_ctor_get(v_a_948_, 5);
        v___x_957_ = 0;
        v___x_958_ = l_Lean_SourceInfo_fromRef(v_ref_956_, v___x_957_);
        v___x_959_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_960_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7;
        crate::leanh::lean_inc_n(v___x_958_, 10);
        v___x_961_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_961_, 0, v___x_958_);
        crate::leanh::lean_ctor_set(v___x_961_, 1, v___x_960_);
        v___x_962_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9;
        v___x_963_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_964_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_965_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14;
        v___x_966_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_967_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_967_, 0, v___x_958_);
        crate::leanh::lean_ctor_set(v___x_967_, 1, v___x_965_);
        v___x_968_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1), core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once), _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1);
        v___x_969_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_955_);
        crate::leanh::lean_inc(v_quotContext_954_);
        v___x_970_ = l_Lean_addMacroScope(v_quotContext_954_, v___x_969_, v_currMacroScope_955_);
        v___x_971_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5;
        v___x_972_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_972_, 0, v___x_958_);
        crate::leanh::lean_ctor_set(v___x_972_, 1, v___x_968_);
        crate::leanh::lean_ctor_set(v___x_972_, 2, v___x_970_);
        crate::leanh::lean_ctor_set(v___x_972_, 3, v___x_971_);
        v___x_973_ = l_Lean_Syntax_node2(v___x_958_, v___x_966_, v___x_967_, v___x_972_);
        v___x_974_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_975_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_975_, 0, v___x_958_);
        crate::leanh::lean_ctor_set(v___x_975_, 1, v___x_974_);
        v___x_976_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26;
        v___x_977_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_978_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_978_, 0, v___x_958_);
        crate::leanh::lean_ctor_set(v___x_978_, 1, v___x_976_);
        v___x_979_ = l_Lean_Syntax_node1(v___x_958_, v___x_977_, v___x_978_);
        v___x_980_ =
            l_Lean_Syntax_node3(v___x_958_, v___x_964_, v___x_973_, v___x_975_, v___x_979_);
        v___x_981_ = l_Lean_Syntax_node1(v___x_958_, v___x_963_, v___x_980_);
        v___x_982_ = l_Lean_Syntax_node1(v___x_958_, v___x_962_, v___x_981_);
        v___x_983_ = l_Lean_Syntax_node2(v___x_958_, v___x_959_, v___x_961_, v___x_982_);
        v___x_984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_984_, 0, v___x_983_);
        crate::leanh::lean_ctor_set(v___x_984_, 1, v_a_949_);
        return v___x_984_;
    }
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___boxed(
    mut v_x_985_: *mut crate::leanh::LeanObject,
    mut v_a_986_: *mut crate::leanh::LeanObject,
    mut v_a_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(v_x_985_, v_a_986_, v_a_987_);
    crate::leanh::lean_dec_ref(v_a_986_);
    return v_res_988_;
}
pub unsafe fn l_String_Legacy_Iterator_setCurr(
    mut v_x_989_: *mut crate::leanh::LeanObject,
    mut v_x_990_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_991_ = crate::leanh::lean_ctor_get(v_x_989_, 0);
                v_i_992_ = crate::leanh::lean_ctor_get(v_x_989_, 1);
                v_isSharedCheck_1000_ = (!crate::leanh::lean_is_exclusive(v_x_989_)) as u8;
                if v_isSharedCheck_1000_ == 0 {
                    v___x_994_ = v_x_989_;
                    v_isShared_995_ = v_isSharedCheck_1000_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_i_992_);
                    crate::leanh::lean_inc(v_s_991_);
                    crate::leanh::lean_dec(v_x_989_);
                    v___x_994_ = crate::leanh::lean_box(0);
                    v_isShared_995_ = v_isSharedCheck_1000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_996_ = lean_string_utf8_set(v_s_991_, v_i_992_, v_x_990_);
                if v_isShared_995_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_994_, 0, v___x_996_);
                    v___x_998_ = v___x_994_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_999_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_999_, 1, v_i_992_);
                    v___x_998_ = v_reuseFailAlloc_999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_setCurr___boxed(
    mut v_x_1001_: *mut crate::leanh::LeanObject,
    mut v_x_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_15__boxed_1003_: u32 = 0;
    let mut v_res_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_15__boxed_1003_ = crate::leanh::lean_unbox_uint32(v_x_1002_);
    crate::leanh::lean_dec(v_x_1002_);
    v_res_1004_ = l_String_Legacy_Iterator_setCurr(v_x_1001_, v_x_15__boxed_1003_);
    return v_res_1004_;
}
pub unsafe fn l_String_Legacy_Iterator_find(
    mut v_it_1005_: *mut crate::leanh::LeanObject,
    mut v_p_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: u8 = 0;
    let mut v___x_1011_: u32 = 0;
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1017_: u8 = 0;
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1023_: u8 = 0;
    let mut v_unused_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1007_ = crate::leanh::lean_ctor_get(v_it_1005_, 0);
                v_i_1008_ = crate::leanh::lean_ctor_get(v_it_1005_, 1);
                v___x_1009_ = lean_string_utf8_byte_size(v_s_1007_);
                v___x_1010_ = lean_nat_dec_le(v___x_1009_, v_i_1008_);
                if v___x_1010_ == 0 {
                    v___x_1011_ = lean_string_utf8_get(v_s_1007_, v_i_1008_);
                    v___x_1012_ = crate::leanh::lean_box_uint32(v___x_1011_);
                    crate::leanh::lean_inc_ref(v_p_1006_);
                    v___x_1013_ = crate::leanh::lean_apply_1(v_p_1006_, v___x_1012_);
                    v___x_1014_ = (crate::leanh::lean_unbox(v___x_1013_) as u8);
                    if v___x_1014_ == 0 {
                        crate::leanh::lean_inc(v_i_1008_);
                        crate::leanh::lean_inc_ref(v_s_1007_);
                        v_isSharedCheck_1023_ =
                            (!crate::leanh::lean_is_exclusive(v_it_1005_)) as u8;
                        if v_isSharedCheck_1023_ == 0 {
                            v_unused_1024_ = crate::leanh::lean_ctor_get(v_it_1005_, 1);
                            crate::leanh::lean_dec(v_unused_1024_);
                            v_unused_1025_ = crate::leanh::lean_ctor_get(v_it_1005_, 0);
                            crate::leanh::lean_dec(v_unused_1025_);
                            v___x_1016_ = v_it_1005_;
                            v_isShared_1017_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_it_1005_);
                            v___x_1016_ = crate::leanh::lean_box(0);
                            v_isShared_1017_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_1006_);
                        return v_it_1005_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_1006_);
                    return v_it_1005_;
                }
            }
            1 => {
                v___x_1018_ = lean_string_utf8_next(v_s_1007_, v_i_1008_);
                crate::leanh::lean_dec(v_i_1008_);
                if v_isShared_1017_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1016_, 1, v___x_1018_);
                    v___x_1020_ = v___x_1016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_s_1007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1018_);
                    v___x_1020_ = v_reuseFailAlloc_1022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_it_1005_ = v___x_1020_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_foldUntil___redArg(
    mut v_it_1026_: *mut crate::leanh::LeanObject,
    mut v_init_1027_: *mut crate::leanh::LeanObject,
    mut v_f_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: u32 = 0;
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v_val_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut v_unused_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1029_ = crate::leanh::lean_ctor_get(v_it_1026_, 0);
                v_i_1030_ = crate::leanh::lean_ctor_get(v_it_1026_, 1);
                v___x_1031_ = lean_string_utf8_byte_size(v_s_1029_);
                v___x_1032_ = lean_nat_dec_le(v___x_1031_, v_i_1030_);
                if v___x_1032_ == 0 {
                    v___x_1033_ = lean_string_utf8_get(v_s_1029_, v_i_1030_);
                    v___x_1034_ = crate::leanh::lean_box_uint32(v___x_1033_);
                    crate::leanh::lean_inc_ref(v_f_1028_);
                    crate::leanh::lean_inc(v_init_1027_);
                    v___x_1035_ = crate::leanh::lean_apply_2(v_f_1028_, v_init_1027_, v___x_1034_);
                    if crate::leanh::lean_obj_tag(v___x_1035_) == 1 {
                        crate::leanh::lean_inc(v_i_1030_);
                        crate::leanh::lean_inc_ref(v_s_1029_);
                        crate::leanh::lean_dec(v_init_1027_);
                        v_isSharedCheck_1045_ =
                            (!crate::leanh::lean_is_exclusive(v_it_1026_)) as u8;
                        if v_isSharedCheck_1045_ == 0 {
                            v_unused_1046_ = crate::leanh::lean_ctor_get(v_it_1026_, 1);
                            crate::leanh::lean_dec(v_unused_1046_);
                            v_unused_1047_ = crate::leanh::lean_ctor_get(v_it_1026_, 0);
                            crate::leanh::lean_dec(v_unused_1047_);
                            v___x_1037_ = v_it_1026_;
                            v_isShared_1038_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_it_1026_);
                            v___x_1037_ = crate::leanh::lean_box(0);
                            v_isShared_1038_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1035_);
                        crate::leanh::lean_dec_ref(v_f_1028_);
                        v___x_1048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1048_, 0, v_init_1027_);
                        crate::leanh::lean_ctor_set(v___x_1048_, 1, v_it_1026_);
                        return v___x_1048_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_1028_);
                    v___x_1049_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1049_, 0, v_init_1027_);
                    crate::leanh::lean_ctor_set(v___x_1049_, 1, v_it_1026_);
                    return v___x_1049_;
                }
            }
            1 => {
                v_val_1039_ = crate::leanh::lean_ctor_get(v___x_1035_, 0);
                crate::leanh::lean_inc(v_val_1039_);
                crate::leanh::lean_dec_ref_known(v___x_1035_, 1);
                v___x_1040_ = lean_string_utf8_next(v_s_1029_, v_i_1030_);
                crate::leanh::lean_dec(v_i_1030_);
                if v_isShared_1038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1037_, 1, v___x_1040_);
                    v___x_1042_ = v___x_1037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1044_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_s_1029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1040_);
                    v___x_1042_ = v_reuseFailAlloc_1044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_it_1026_ = v___x_1042_;
                v_init_1027_ = v_val_1039_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_foldUntil(
    mut v_00_u03b1_1050_: *mut crate::leanh::LeanObject,
    mut v_it_1051_: *mut crate::leanh::LeanObject,
    mut v_init_1052_: *mut crate::leanh::LeanObject,
    mut v_f_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_String_Legacy_Iterator_foldUntil___redArg(v_it_1051_, v_init_1052_, v_f_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter___redArg(
    mut v_x_1055_: *mut crate::leanh::LeanObject,
    mut v_h__1_1056_: *mut crate::leanh::LeanObject,
    mut v_h__2_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1055_) == 1 {
        let mut v_val_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1057_);
        v_val_1058_ = crate::leanh::lean_ctor_get(v_x_1055_, 0);
        crate::leanh::lean_inc(v_val_1058_);
        crate::leanh::lean_dec_ref_known(v_x_1055_, 1);
        v___x_1059_ = crate::leanh::lean_apply_1(v_h__1_1056_, v_val_1058_);
        return v___x_1059_;
    } else {
        let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1056_);
        v___x_1060_ =
            crate::leanh::lean_apply_2(v_h__2_1057_, v_x_1055_, crate::leanh::lean_box(0));
        return v___x_1060_;
    }
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter(
    mut v_00_u03b1_1061_: *mut crate::leanh::LeanObject,
    mut v_motive_1062_: *mut crate::leanh::LeanObject,
    mut v_x_1063_: *mut crate::leanh::LeanObject,
    mut v_h__1_1064_: *mut crate::leanh::LeanObject,
    mut v_h__2_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1063_) == 1 {
        let mut v_val_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1065_);
        v_val_1066_ = crate::leanh::lean_ctor_get(v_x_1063_, 0);
        crate::leanh::lean_inc(v_val_1066_);
        crate::leanh::lean_dec_ref_known(v_x_1063_, 1);
        v___x_1067_ = crate::leanh::lean_apply_1(v_h__1_1064_, v_val_1066_);
        return v___x_1067_;
    } else {
        let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1064_);
        v___x_1068_ =
            crate::leanh::lean_apply_2(v_h__2_1065_, v_x_1063_, crate::leanh::lean_box(0));
        return v___x_1068_;
    }
}
pub unsafe fn l_Substring_Raw_toLegacyIterator(
    mut v_x_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_1070_ = crate::leanh::lean_ctor_get(v_x_1069_, 0);
    v_startPos_1071_ = crate::leanh::lean_ctor_get(v_x_1069_, 1);
    crate::leanh::lean_inc(v_startPos_1071_);
    crate::leanh::lean_inc_ref(v_str_1070_);
    v___x_1072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1072_, 0, v_str_1070_);
    crate::leanh::lean_ctor_set(v___x_1072_, 1, v_startPos_1071_);
    return v___x_1072_;
}
pub unsafe fn l_Substring_Raw_toLegacyIterator___boxed(
    mut v_x_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Substring_Raw_toLegacyIterator(v_x_1073_);
    crate::leanh::lean_dec_ref(v_x_1073_);
    return v_res_1074_;
}
pub unsafe fn l_instReprIterator___lam__0(
    mut v_x_1087_: *mut crate::leanh::LeanObject,
    mut v_x_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1089_ = crate::leanh::lean_ctor_get(v_x_1087_, 0);
                v_i_1090_ = crate::leanh::lean_ctor_get(v_x_1087_, 1);
                v_isSharedCheck_1110_ = (!crate::leanh::lean_is_exclusive(v_x_1087_)) as u8;
                if v_isSharedCheck_1110_ == 0 {
                    v___x_1092_ = v_x_1087_;
                    v_isShared_1093_ = v_isSharedCheck_1110_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_i_1090_);
                    crate::leanh::lean_inc(v_s_1089_);
                    crate::leanh::lean_dec(v_x_1087_);
                    v___x_1092_ = crate::leanh::lean_box(0);
                    v_isShared_1093_ = v_isSharedCheck_1110_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1094_ = l_instReprIterator___lam__0___closed__1;
                v___x_1095_ = l_String_quote(v_s_1089_);
                v___x_1096_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1096_, 0, v___x_1095_);
                if v_isShared_1093_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1092_, 5);
                    crate::leanh::lean_ctor_set(v___x_1092_, 1, v___x_1096_);
                    crate::leanh::lean_ctor_set(v___x_1092_, 0, v___x_1094_);
                    v___x_1098_ = v___x_1092_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1109_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1096_);
                    v___x_1098_ = v_reuseFailAlloc_1109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1099_ = l_instReprIterator___lam__0___closed__3;
                v___x_1100_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1100_, 0, v___x_1098_);
                crate::leanh::lean_ctor_set(v___x_1100_, 1, v___x_1099_);
                v___x_1101_ = l_instReprIterator___lam__0___closed__5;
                v___x_1102_ = l_Nat_reprFast(v_i_1090_);
                v___x_1103_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1103_, 0, v___x_1102_);
                v___x_1104_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1104_, 0, v___x_1101_);
                crate::leanh::lean_ctor_set(v___x_1104_, 1, v___x_1103_);
                v___x_1105_ = l_instReprIterator___lam__0___closed__7;
                v___x_1106_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1106_, 0, v___x_1104_);
                crate::leanh::lean_ctor_set(v___x_1106_, 1, v___x_1105_);
                v___x_1107_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1107_, 0, v___x_1100_);
                crate::leanh::lean_ctor_set(v___x_1107_, 1, v___x_1106_);
                v___x_1108_ = l_Repr_addAppParen(v___x_1107_, v_x_1088_);
                return v___x_1108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instReprIterator___lam__0___boxed(
    mut v_x_1111_: *mut crate::leanh::LeanObject,
    mut v_x_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_instReprIterator___lam__0(v_x_1111_, v_x_1112_);
    crate::leanh::lean_dec(v_x_1112_);
    return v_res_1113_;
}
pub unsafe fn l_instToStringIterator___lam__0(
    mut v_it_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_1117_ = crate::leanh::lean_ctor_get(v_it_1116_, 0);
    v_i_1118_ = crate::leanh::lean_ctor_get(v_it_1116_, 1);
    v___x_1119_ = lean_string_utf8_byte_size(v_s_1117_);
    v___x_1120_ = lean_string_utf8_extract(v_s_1117_, v_i_1118_, v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn l_instToStringIterator___lam__0___boxed(
    mut v_it_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_instToStringIterator___lam__0(v_it_1121_);
    crate::leanh::lean_dec_ref(v_it_1121_);
    return v_res_1122_;
}
pub unsafe fn l_String_iter(
    mut v_s_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1127_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1127_, 0, v_s_1125_);
    crate::leanh::lean_ctor_set(v___x_1127_, 1, v___x_1126_);
    return v___x_1127_;
}
pub unsafe fn l_String_mkIterator(
    mut v_s_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1130_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1130_, 0, v_s_1128_);
    crate::leanh::lean_ctor_set(v___x_1130_, 1, v___x_1129_);
    return v___x_1130_;
}
pub unsafe fn l_String_Iterator_curr(mut v_a_1131_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v_s_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: u32 = 0;
    v_s_1132_ = crate::leanh::lean_ctor_get(v_a_1131_, 0);
    v_i_1133_ = crate::leanh::lean_ctor_get(v_a_1131_, 1);
    v___x_1134_ = lean_string_utf8_get(v_s_1132_, v_i_1133_);
    return v___x_1134_;
}
pub unsafe fn l_String_Iterator_curr___boxed(
    mut v_a_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1136_: u32 = 0;
    let mut v_r_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1136_ = l_String_Iterator_curr(v_a_1135_);
    crate::leanh::lean_dec_ref(v_a_1135_);
    v_r_1137_ = crate::leanh::lean_box_uint32(v_res_1136_);
    return v_r_1137_;
}
pub unsafe fn l_String_Iterator_next(
    mut v_a_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1139_ = crate::leanh::lean_ctor_get(v_a_1138_, 0);
                v_i_1140_ = crate::leanh::lean_ctor_get(v_a_1138_, 1);
                v_isSharedCheck_1148_ = (!crate::leanh::lean_is_exclusive(v_a_1138_)) as u8;
                if v_isSharedCheck_1148_ == 0 {
                    v___x_1142_ = v_a_1138_;
                    v_isShared_1143_ = v_isSharedCheck_1148_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_i_1140_);
                    crate::leanh::lean_inc(v_s_1139_);
                    crate::leanh::lean_dec(v_a_1138_);
                    v___x_1142_ = crate::leanh::lean_box(0);
                    v_isShared_1143_ = v_isSharedCheck_1148_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1144_ = lean_string_utf8_next(v_s_1139_, v_i_1140_);
                crate::leanh::lean_dec(v_i_1140_);
                if v_isShared_1143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1142_, 1, v___x_1144_);
                    v___x_1146_ = v___x_1142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_s_1139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1144_);
                    v___x_1146_ = v_reuseFailAlloc_1147_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Iterator_hasNext(mut v_a_1149_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_s_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    v_s_1150_ = crate::leanh::lean_ctor_get(v_a_1149_, 0);
    v_i_1151_ = crate::leanh::lean_ctor_get(v_a_1149_, 1);
    v___x_1152_ = lean_string_utf8_byte_size(v_s_1150_);
    v___x_1153_ = lean_nat_dec_lt(v_i_1151_, v___x_1152_);
    return v___x_1153_;
}
pub unsafe fn l_String_Iterator_hasNext___boxed(
    mut v_a_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1155_: u8 = 0;
    let mut v_r_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_String_Iterator_hasNext(v_a_1154_);
    crate::leanh::lean_dec_ref(v_a_1154_);
    v_r_1156_ = crate::leanh::lean_box((v_res_1155_) as usize);
    return v_r_1156_;
}
pub unsafe fn l_Substring_toIterator(
    mut v_a_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_str_1158_ = crate::leanh::lean_ctor_get(v_a_1157_, 0);
    v_startPos_1159_ = crate::leanh::lean_ctor_get(v_a_1157_, 1);
    crate::leanh::lean_inc(v_startPos_1159_);
    crate::leanh::lean_inc_ref(v_str_1158_);
    v___x_1160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1160_, 0, v_str_1158_);
    crate::leanh::lean_ctor_set(v___x_1160_, 1, v_startPos_1159_);
    return v___x_1160_;
}
pub unsafe fn l_Substring_toIterator___boxed(
    mut v_a_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Substring_toIterator(v_a_1161_);
    crate::leanh::lean_dec_ref(v_a_1161_);
    return v_res_1162_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Iterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Iterator(
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
pub unsafe fn initialize_Init_Data_String_Iterator(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Iterator(builtin);
}
