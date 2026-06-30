// Lean compiler output
// Module: Init.Data.String.Iterator
// Imports: Init.Data.String.Modify
use crate::ffi::{
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next, lean_string_utf8_next_fast,
    lean_string_utf8_prev, lean_string_utf8_set,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
pub static l_String_Legacy_instInhabitedIterator_default___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_Legacy_instInhabitedIterator_default___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_String_Legacy_instInhabitedIterator_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_String_Legacy_instInhabitedIterator_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_String_Legacy_instInhabitedIterator: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_String_Legacy_instSizeOfIterator___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_Legacy_instSizeOfIterator___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_Legacy_instSizeOfIterator___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instSizeOfIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_String_Legacy_instSizeOfIterator: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instSizeOfIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114, 105, 118, 105, 97, 108, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut leanh::LeanObject,5744670087858236374 as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut leanh::LeanObject,6022092293134036165 as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value) as *mut leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value) as *mut leanh::LeanObject,8504843326314613972 as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut leanh::LeanObject,17228437386856258271 as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut leanh::LeanObject,5826123769708379594 as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16_value: leanh::LeanStringObject<49> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [83, 116, 114, 105, 110, 103, 46, 76, 101, 103, 97, 99, 121, 46, 73, 116, 101, 114, 97, 116, 111, 114, 46, 115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 104, 97, 115, 78, 101, 120, 116, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16_value) as *mut leanh::LeanObject;
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 105, 110, 103, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 101, 103, 97, 99, 121, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 116, 101, 114, 97, 116, 111, 114, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 104, 97, 115, 78, 101, 120, 116, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value) as *mut leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut leanh::LeanObject,3136308715950998022 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut leanh::LeanObject,16221383843924677366 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut leanh::LeanObject,13785796134284214332 as *mut leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value) as *mut leanh::LeanObject,17921308319265575761 as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut leanh::LeanObject,16687334436616221424 as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0_value: leanh::LeanStringObject<47> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [83, 116, 114, 105, 110, 103, 46, 76, 101, 103, 97, 99, 121, 46, 73, 116, 101, 114, 97, 116, 111, 114, 46, 115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 97, 116, 69, 110, 100, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0_value) as *mut leanh::LeanObject;
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 97, 116, 69, 110, 100, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut leanh::LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut leanh::LeanObject,3136308715950998022 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut leanh::LeanObject,16221383843924677366 as *mut leanh::LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut leanh::LeanObject,13785796134284214332 as *mut leanh::LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut leanh::LeanObject,4155438117962710745 as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut leanh::LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5_value) as *mut leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__0_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprIterator___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprIterator___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprIterator___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprIterator___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprIterator___lam__0___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprIterator___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__4_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprIterator___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprIterator___lam__0___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprIterator___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__6_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprIterator___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_instReprIterator___lam__0___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprIterator___lam__0___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprIterator___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_instReprIterator___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instReprIterator___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprIterator___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprIterator: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprIterator___closed__0_value) as *mut leanh::LeanObject;
pub static l_instToStringIterator___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringIterator___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringIterator___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringIterator___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instToStringIterator: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringIterator___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_String_Legacy_instDecidableEqIterator_decEq(
    mut v_x_582_: *mut leanh::LeanObject,
    mut v_x_583_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_s_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    v_s_584_ = leanh::lean_ctor_get(v_x_582_, 0);
    v_i_585_ = leanh::lean_ctor_get(v_x_582_, 1);
    v_s_586_ = leanh::lean_ctor_get(v_x_583_, 0);
    v_i_587_ = leanh::lean_ctor_get(v_x_583_, 1);
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
    mut v_x_590_: *mut leanh::LeanObject,
    mut v_x_591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_592_: u8 = 0;
    let mut v_r_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_592_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_590_, v_x_591_);
    leanh::lean_dec_ref(v_x_591_);
    leanh::lean_dec_ref(v_x_590_);
    v_r_593_ = leanh::lean_box((v_res_592_) as usize);
    return v_r_593_;
}
pub unsafe fn l_String_Legacy_instDecidableEqIterator(
    mut v_x_594_: *mut leanh::LeanObject,
    mut v_x_595_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_596_: u8 = 0;
    v___x_596_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_594_, v_x_595_);
    return v___x_596_;
}
pub unsafe fn l_String_Legacy_instDecidableEqIterator___boxed(
    mut v_x_597_: *mut leanh::LeanObject,
    mut v_x_598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_599_: u8 = 0;
    let mut v_r_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_599_ = l_String_Legacy_instDecidableEqIterator(v_x_597_, v_x_598_);
    leanh::lean_dec_ref(v_x_598_);
    leanh::lean_dec_ref(v_x_597_);
    v_r_600_ = leanh::lean_box((v_res_599_) as usize);
    return v_r_600_;
}
pub unsafe fn l_String_Legacy_mkIterator(
    mut v_s_607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = leanh::lean_unsigned_to_nat(0);
    v___x_609_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_609_, 0, v_s_607_);
    leanh::lean_ctor_set(v___x_609_, 1, v___x_608_);
    return v___x_609_;
}
pub unsafe fn l_String_Legacy_iter(
    mut v_s_610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_611_ = leanh::lean_unsigned_to_nat(0);
    v___x_612_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_612_, 0, v_s_610_);
    leanh::lean_ctor_set(v___x_612_, 1, v___x_611_);
    return v___x_612_;
}
pub unsafe fn l_String_Legacy_instSizeOfIterator___lam__0(
    mut v_i_613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_614_ = leanh::lean_ctor_get(v_i_613_, 0);
    v_i_615_ = leanh::lean_ctor_get(v_i_613_, 1);
    v___x_616_ = lean_string_utf8_byte_size(v_s_614_);
    v___x_617_ = lean_nat_sub(v___x_616_, v_i_615_);
    return v___x_617_;
}
pub unsafe fn l_String_Legacy_instSizeOfIterator___lam__0___boxed(
    mut v_i_618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_619_ = l_String_Legacy_instSizeOfIterator___lam__0(v_i_618_);
    leanh::lean_dec_ref(v_i_618_);
    return v_res_619_;
}
pub unsafe fn l_String_Legacy_Iterator_toString(
    mut v_self_622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_623_ = leanh::lean_ctor_get(v_self_622_, 0);
    leanh::lean_inc_ref(v_s_623_);
    return v_s_623_;
}
pub unsafe fn l_String_Legacy_Iterator_toString___boxed(
    mut v_self_624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_625_ = l_String_Legacy_Iterator_toString(v_self_624_);
    leanh::lean_dec_ref(v_self_624_);
    return v_res_625_;
}
pub unsafe fn l_String_Legacy_Iterator_remainingBytes(
    mut v_x_626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_627_ = leanh::lean_ctor_get(v_x_626_, 0);
    v_i_628_ = leanh::lean_ctor_get(v_x_626_, 1);
    v___x_629_ = lean_string_utf8_byte_size(v_s_627_);
    v___x_630_ = lean_nat_sub(v___x_629_, v_i_628_);
    return v___x_630_;
}
pub unsafe fn l_String_Legacy_Iterator_remainingBytes___boxed(
    mut v_x_631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_632_ = l_String_Legacy_Iterator_remainingBytes(v_x_631_);
    leanh::lean_dec_ref(v_x_631_);
    return v_res_632_;
}
pub unsafe fn l_String_Legacy_Iterator_pos(
    mut v_self_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_634_ = leanh::lean_ctor_get(v_self_633_, 1);
    leanh::lean_inc(v_i_634_);
    return v_i_634_;
}
pub unsafe fn l_String_Legacy_Iterator_pos___boxed(
    mut v_self_635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_636_ = l_String_Legacy_Iterator_pos(v_self_635_);
    leanh::lean_dec_ref(v_self_635_);
    return v_res_636_;
}
pub unsafe fn l_String_Legacy_Iterator_curr(mut v_x_637_: *mut leanh::LeanObject) -> u32 {
    let mut v_s_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: u32 = 0;
    v_s_638_ = leanh::lean_ctor_get(v_x_637_, 0);
    v_i_639_ = leanh::lean_ctor_get(v_x_637_, 1);
    v___x_640_ = lean_string_utf8_get(v_s_638_, v_i_639_);
    return v___x_640_;
}
pub unsafe fn l_String_Legacy_Iterator_curr___boxed(
    mut v_x_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_642_: u32 = 0;
    let mut v_r_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ = l_String_Legacy_Iterator_curr(v_x_641_);
    leanh::lean_dec_ref(v_x_641_);
    v_r_643_ = leanh::lean_box_uint32(v_res_642_);
    return v_r_643_;
}
pub unsafe fn l_String_Legacy_Iterator_next(
    mut v_x_644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_645_ = leanh::lean_ctor_get(v_x_644_, 0);
                v_i_646_ = leanh::lean_ctor_get(v_x_644_, 1);
                v_isSharedCheck_654_ = (!leanh::lean_is_exclusive(v_x_644_)) as u8;
                if v_isSharedCheck_654_ == 0 {
                    v___x_648_ = v_x_644_;
                    v_isShared_649_ = v_isSharedCheck_654_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_i_646_);
                    leanh::lean_inc(v_s_645_);
                    leanh::lean_dec(v_x_644_);
                    v___x_648_ = leanh::lean_box(0);
                    v_isShared_649_ = v_isSharedCheck_654_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_650_ = lean_string_utf8_next(v_s_645_, v_i_646_);
                leanh::lean_dec(v_i_646_);
                if v_isShared_649_ == 0 {
                    leanh::lean_ctor_set(v___x_648_, 1, v___x_650_);
                    v___x_652_ = v___x_648_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v_s_645_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
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
    mut v_x_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_656_ = leanh::lean_ctor_get(v_x_655_, 0);
                v_i_657_ = leanh::lean_ctor_get(v_x_655_, 1);
                v_isSharedCheck_665_ = (!leanh::lean_is_exclusive(v_x_655_)) as u8;
                if v_isSharedCheck_665_ == 0 {
                    v___x_659_ = v_x_655_;
                    v_isShared_660_ = v_isSharedCheck_665_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_i_657_);
                    leanh::lean_inc(v_s_656_);
                    leanh::lean_dec(v_x_655_);
                    v___x_659_ = leanh::lean_box(0);
                    v_isShared_660_ = v_isSharedCheck_665_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_661_ = lean_string_utf8_prev(v_s_656_, v_i_657_);
                leanh::lean_dec(v_i_657_);
                if v_isShared_660_ == 0 {
                    leanh::lean_ctor_set(v___x_659_, 1, v___x_661_);
                    v___x_663_ = v___x_659_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_664_, 0, v_s_656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
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
pub unsafe fn l_String_Legacy_Iterator_atEnd(mut v_x_666_: *mut leanh::LeanObject) -> u8 {
    let mut v_s_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: u8 = 0;
    v_s_667_ = leanh::lean_ctor_get(v_x_666_, 0);
    v_i_668_ = leanh::lean_ctor_get(v_x_666_, 1);
    v___x_669_ = lean_string_utf8_byte_size(v_s_667_);
    v___x_670_ = lean_nat_dec_le(v___x_669_, v_i_668_);
    return v___x_670_;
}
pub unsafe fn l_String_Legacy_Iterator_atEnd___boxed(
    mut v_x_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_672_: u8 = 0;
    let mut v_r_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_672_ = l_String_Legacy_Iterator_atEnd(v_x_671_);
    leanh::lean_dec_ref(v_x_671_);
    v_r_673_ = leanh::lean_box((v_res_672_) as usize);
    return v_r_673_;
}
pub unsafe fn l_String_Legacy_Iterator_hasNext(mut v_x_674_: *mut leanh::LeanObject) -> u8 {
    let mut v_s_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u8 = 0;
    v_s_675_ = leanh::lean_ctor_get(v_x_674_, 0);
    v_i_676_ = leanh::lean_ctor_get(v_x_674_, 1);
    v___x_677_ = lean_string_utf8_byte_size(v_s_675_);
    v___x_678_ = lean_nat_dec_lt(v_i_676_, v___x_677_);
    return v___x_678_;
}
pub unsafe fn l_String_Legacy_Iterator_hasNext___boxed(
    mut v_x_679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_680_: u8 = 0;
    let mut v_r_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_680_ = l_String_Legacy_Iterator_hasNext(v_x_679_);
    leanh::lean_dec_ref(v_x_679_);
    v_r_681_ = leanh::lean_box((v_res_680_) as usize);
    return v_r_681_;
}
pub unsafe fn l_String_Legacy_Iterator_hasPrev(mut v_x_682_: *mut leanh::LeanObject) -> u8 {
    let mut v_i_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    v_i_683_ = leanh::lean_ctor_get(v_x_682_, 1);
    v___x_684_ = leanh::lean_unsigned_to_nat(0);
    v___x_685_ = lean_nat_dec_lt(v___x_684_, v_i_683_);
    return v___x_685_;
}
pub unsafe fn l_String_Legacy_Iterator_hasPrev___boxed(
    mut v_x_686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_687_: u8 = 0;
    let mut v_r_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_687_ = l_String_Legacy_Iterator_hasPrev(v_x_686_);
    leanh::lean_dec_ref(v_x_686_);
    v_r_688_ = leanh::lean_box((v_res_687_) as usize);
    return v_r_688_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter___redArg(
    mut v_x_689_: *mut leanh::LeanObject,
    mut v_h__1_690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_691_ = leanh::lean_ctor_get(v_x_689_, 0);
    leanh::lean_inc_ref(v_s_691_);
    v_i_692_ = leanh::lean_ctor_get(v_x_689_, 1);
    leanh::lean_inc(v_i_692_);
    leanh::lean_dec_ref(v_x_689_);
    v___x_693_ = leanh::lean_apply_2(v_h__1_690_, v_s_691_, v_i_692_);
    return v___x_693_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter(
    mut v_motive_694_: *mut leanh::LeanObject,
    mut v_x_695_: *mut leanh::LeanObject,
    mut v_h__1_696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_697_ = leanh::lean_ctor_get(v_x_695_, 0);
    leanh::lean_inc_ref(v_s_697_);
    v_i_698_ = leanh::lean_ctor_get(v_x_695_, 1);
    leanh::lean_inc(v_i_698_);
    leanh::lean_dec_ref(v_x_695_);
    v___x_699_ = leanh::lean_apply_2(v_h__1_696_, v_s_697_, v_i_698_);
    return v___x_699_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(
    mut v_x_700_: *mut leanh::LeanObject,
    mut v_x_701_: *mut leanh::LeanObject,
    mut v_h__1_702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = leanh::lean_apply_2(v_h__1_702_, v_x_700_, v_x_701_);
    return v___x_703_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter(
    mut v_motive_704_: *mut leanh::LeanObject,
    mut v_x_705_: *mut leanh::LeanObject,
    mut v_x_706_: *mut leanh::LeanObject,
    mut v_h__1_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = leanh::lean_apply_2(v_h__1_707_, v_x_705_, v_x_706_);
    return v___x_708_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27___redArg(
    mut v_it_709_: *mut leanh::LeanObject,
) -> u32 {
    let mut v_s_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u32 = 0;
    v_s_710_ = leanh::lean_ctor_get(v_it_709_, 0);
    v_i_711_ = leanh::lean_ctor_get(v_it_709_, 1);
    v___x_712_ = lean_string_utf8_get_fast(v_s_710_, v_i_711_);
    return v___x_712_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27___redArg___boxed(
    mut v_it_713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_714_: u32 = 0;
    let mut v_r_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_714_ = l_String_Legacy_Iterator_curr_x27___redArg(v_it_713_);
    leanh::lean_dec_ref(v_it_713_);
    v_r_715_ = leanh::lean_box_uint32(v_res_714_);
    return v_r_715_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27(
    mut v_it_716_: *mut leanh::LeanObject,
    mut v_h_717_: *mut leanh::LeanObject,
) -> u32 {
    let mut v_s_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u32 = 0;
    v_s_718_ = leanh::lean_ctor_get(v_it_716_, 0);
    v_i_719_ = leanh::lean_ctor_get(v_it_716_, 1);
    v___x_720_ = lean_string_utf8_get_fast(v_s_718_, v_i_719_);
    return v___x_720_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27___boxed(
    mut v_it_721_: *mut leanh::LeanObject,
    mut v_h_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_723_: u32 = 0;
    let mut v_r_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ = l_String_Legacy_Iterator_curr_x27(v_it_721_, v_h_722_);
    leanh::lean_dec_ref(v_it_721_);
    v_r_724_ = leanh::lean_box_uint32(v_res_723_);
    return v_r_724_;
}
pub unsafe fn l_String_Legacy_Iterator_next_x27___redArg(
    mut v_it_725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_726_ = leanh::lean_ctor_get(v_it_725_, 0);
                v_i_727_ = leanh::lean_ctor_get(v_it_725_, 1);
                v_isSharedCheck_735_ = (!leanh::lean_is_exclusive(v_it_725_)) as u8;
                if v_isSharedCheck_735_ == 0 {
                    v___x_729_ = v_it_725_;
                    v_isShared_730_ = v_isSharedCheck_735_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_i_727_);
                    leanh::lean_inc(v_s_726_);
                    leanh::lean_dec(v_it_725_);
                    v___x_729_ = leanh::lean_box(0);
                    v_isShared_730_ = v_isSharedCheck_735_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_731_ = lean_string_utf8_next_fast(v_s_726_, v_i_727_);
                leanh::lean_dec(v_i_727_);
                if v_isShared_730_ == 0 {
                    leanh::lean_ctor_set(v___x_729_, 1, v___x_731_);
                    v___x_733_ = v___x_729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_734_, 0, v_s_726_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_731_);
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
    mut v_it_736_: *mut leanh::LeanObject,
    mut v_h_737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_738_ = leanh::lean_ctor_get(v_it_736_, 0);
                v_i_739_ = leanh::lean_ctor_get(v_it_736_, 1);
                v_isSharedCheck_747_ = (!leanh::lean_is_exclusive(v_it_736_)) as u8;
                if v_isSharedCheck_747_ == 0 {
                    v___x_741_ = v_it_736_;
                    v_isShared_742_ = v_isSharedCheck_747_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_i_739_);
                    leanh::lean_inc(v_s_738_);
                    leanh::lean_dec(v_it_736_);
                    v___x_741_ = leanh::lean_box(0);
                    v_isShared_742_ = v_isSharedCheck_747_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_743_ = lean_string_utf8_next_fast(v_s_738_, v_i_739_);
                leanh::lean_dec(v_i_739_);
                if v_isShared_742_ == 0 {
                    leanh::lean_ctor_set(v___x_741_, 1, v___x_743_);
                    v___x_745_ = v___x_741_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_746_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_746_, 0, v_s_738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_743_);
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
    mut v_x_748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_752_: u8 = 0;
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_757_: u8 = 0;
    let mut v_unused_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_749_ = leanh::lean_ctor_get(v_x_748_, 0);
                v_isSharedCheck_757_ = (!leanh::lean_is_exclusive(v_x_748_)) as u8;
                if v_isSharedCheck_757_ == 0 {
                    v_unused_758_ = leanh::lean_ctor_get(v_x_748_, 1);
                    leanh::lean_dec(v_unused_758_);
                    v___x_751_ = v_x_748_;
                    v_isShared_752_ = v_isSharedCheck_757_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_s_749_);
                    leanh::lean_dec(v_x_748_);
                    v___x_751_ = leanh::lean_box(0);
                    v_isShared_752_ = v_isSharedCheck_757_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_753_ = lean_string_utf8_byte_size(v_s_749_);
                if v_isShared_752_ == 0 {
                    leanh::lean_ctor_set(v___x_751_, 1, v___x_753_);
                    v___x_755_ = v___x_751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_756_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_756_, 0, v_s_749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
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
    mut v_x_759_: *mut leanh::LeanObject,
    mut v_x_760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: u8 = 0;
    v_s_761_ = leanh::lean_ctor_get(v_x_759_, 0);
    v_i_762_ = leanh::lean_ctor_get(v_x_759_, 1);
    v_s_763_ = leanh::lean_ctor_get(v_x_760_, 0);
    v_i_764_ = leanh::lean_ctor_get(v_x_760_, 1);
    v___x_765_ = lean_string_dec_eq(v_s_761_, v_s_763_);
    if v___x_765_ == 0 {
        let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_766_ = l_String_Legacy_instInhabitedIterator_default___closed__0;
        return v___x_766_;
    } else {
        let mut v___x_767_: u8 = 0;
        v___x_767_ = lean_nat_dec_lt(v_i_764_, v_i_762_);
        if v___x_767_ == 0 {
            let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_768_ = lean_string_utf8_extract(v_s_761_, v_i_762_, v_i_764_);
            return v___x_768_;
        } else {
            let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_769_ = l_String_Legacy_instInhabitedIterator_default___closed__0;
            return v___x_769_;
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_extract___boxed(
    mut v_x_770_: *mut leanh::LeanObject,
    mut v_x_771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_772_ = l_String_Legacy_Iterator_extract(v_x_770_, v_x_771_);
    leanh::lean_dec_ref(v_x_771_);
    leanh::lean_dec_ref(v_x_770_);
    return v_res_772_;
}
pub unsafe fn l_String_Legacy_Iterator_forward(
    mut v_x_773_: *mut leanh::LeanObject,
    mut v_x_774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_776_: u8 = 0;
    let mut v_s_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_781_: u8 = 0;
    let mut v_one_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_775_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_776_ = lean_nat_dec_eq(v_x_774_, v_zero_775_);
                if v_isZero_776_ == 1 {
                    leanh::lean_dec(v_x_774_);
                    return v_x_773_;
                } else {
                    v_s_777_ = leanh::lean_ctor_get(v_x_773_, 0);
                    v_i_778_ = leanh::lean_ctor_get(v_x_773_, 1);
                    v_isSharedCheck_789_ = (!leanh::lean_is_exclusive(v_x_773_)) as u8;
                    if v_isSharedCheck_789_ == 0 {
                        v___x_780_ = v_x_773_;
                        v_isShared_781_ = v_isSharedCheck_789_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_778_);
                        leanh::lean_inc(v_s_777_);
                        leanh::lean_dec(v_x_773_);
                        v___x_780_ = leanh::lean_box(0);
                        v_isShared_781_ = v_isSharedCheck_789_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_782_ = leanh::lean_unsigned_to_nat(1);
                v_n_783_ = lean_nat_sub(v_x_774_, v_one_782_);
                leanh::lean_dec(v_x_774_);
                v___x_784_ = lean_string_utf8_next(v_s_777_, v_i_778_);
                leanh::lean_dec(v_i_778_);
                if v_isShared_781_ == 0 {
                    leanh::lean_ctor_set(v___x_780_, 1, v___x_784_);
                    v___x_786_ = v___x_780_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_788_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_788_, 0, v_s_777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_784_);
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
    mut v_x_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_791_ = leanh::lean_ctor_get(v_x_790_, 0);
    v_i_792_ = leanh::lean_ctor_get(v_x_790_, 1);
    v___x_793_ = lean_string_utf8_byte_size(v_s_791_);
    v___x_794_ = lean_string_utf8_extract(v_s_791_, v_i_792_, v___x_793_);
    return v___x_794_;
}
pub unsafe fn l_String_Legacy_Iterator_remainingToString___boxed(
    mut v_x_795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_796_ = l_String_Legacy_Iterator_remainingToString(v_x_795_);
    leanh::lean_dec_ref(v_x_795_);
    return v_res_796_;
}
pub unsafe fn l_String_Legacy_Iterator_nextn(
    mut v_x_797_: *mut leanh::LeanObject,
    mut v_x_798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_800_: u8 = 0;
    let mut v_s_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v_one_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_799_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_800_ = lean_nat_dec_eq(v_x_798_, v_zero_799_);
                if v_isZero_800_ == 1 {
                    leanh::lean_dec(v_x_798_);
                    return v_x_797_;
                } else {
                    v_s_801_ = leanh::lean_ctor_get(v_x_797_, 0);
                    v_i_802_ = leanh::lean_ctor_get(v_x_797_, 1);
                    v_isSharedCheck_813_ = (!leanh::lean_is_exclusive(v_x_797_)) as u8;
                    if v_isSharedCheck_813_ == 0 {
                        v___x_804_ = v_x_797_;
                        v_isShared_805_ = v_isSharedCheck_813_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_802_);
                        leanh::lean_inc(v_s_801_);
                        leanh::lean_dec(v_x_797_);
                        v___x_804_ = leanh::lean_box(0);
                        v_isShared_805_ = v_isSharedCheck_813_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_806_ = leanh::lean_unsigned_to_nat(1);
                v_n_807_ = lean_nat_sub(v_x_798_, v_one_806_);
                leanh::lean_dec(v_x_798_);
                v___x_808_ = lean_string_utf8_next(v_s_801_, v_i_802_);
                leanh::lean_dec(v_i_802_);
                if v_isShared_805_ == 0 {
                    leanh::lean_ctor_set(v___x_804_, 1, v___x_808_);
                    v___x_810_ = v___x_804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_812_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_812_, 0, v_s_801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_808_);
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
    mut v_x_814_: *mut leanh::LeanObject,
    mut v_x_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_817_: u8 = 0;
    let mut v_s_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v_one_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_816_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_817_ = lean_nat_dec_eq(v_x_815_, v_zero_816_);
                if v_isZero_817_ == 1 {
                    leanh::lean_dec(v_x_815_);
                    return v_x_814_;
                } else {
                    v_s_818_ = leanh::lean_ctor_get(v_x_814_, 0);
                    v_i_819_ = leanh::lean_ctor_get(v_x_814_, 1);
                    v_isSharedCheck_830_ = (!leanh::lean_is_exclusive(v_x_814_)) as u8;
                    if v_isSharedCheck_830_ == 0 {
                        v___x_821_ = v_x_814_;
                        v_isShared_822_ = v_isSharedCheck_830_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_819_);
                        leanh::lean_inc(v_s_818_);
                        leanh::lean_dec(v_x_814_);
                        v___x_821_ = leanh::lean_box(0);
                        v_isShared_822_ = v_isSharedCheck_830_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_823_ = leanh::lean_unsigned_to_nat(1);
                v_n_824_ = lean_nat_sub(v_x_815_, v_one_823_);
                leanh::lean_dec(v_x_815_);
                v___x_825_ = lean_string_utf8_prev(v_s_818_, v_i_819_);
                leanh::lean_dec(v_i_819_);
                if v_isShared_822_ == 0 {
                    leanh::lean_ctor_set(v___x_821_, 1, v___x_825_);
                    v___x_827_ = v___x_821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_829_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_829_, 0, v_s_818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_825_);
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
-> *mut leanh::LeanObject {
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16;
    v___x_867_ = l_String_toRawSubstring_x27(v___x_866_);
    return v___x_867_;
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(
    mut v_x_890_: *mut leanh::LeanObject,
    mut v_a_891_: *mut leanh::LeanObject,
    mut v_a_892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: u8 = 0;
    v___x_893_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_894_ = l_Lean_Syntax_isOfKind(v_x_890_, v___x_893_);
    if v___x_894_ == 0 {
        let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_895_ = leanh::lean_box(1);
        v___x_896_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_896_, 0, v___x_895_);
        leanh::lean_ctor_set(v___x_896_, 1, v_a_892_);
        return v___x_896_;
    } else {
        let mut v_quotContext_897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_898_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_900_: u8 = 0;
        let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_897_ = leanh::lean_ctor_get(v_a_891_, 1);
        v_currMacroScope_898_ = leanh::lean_ctor_get(v_a_891_, 2);
        v_ref_899_ = leanh::lean_ctor_get(v_a_891_, 5);
        v___x_900_ = 0;
        v___x_901_ = l_Lean_SourceInfo_fromRef(v_ref_899_, v___x_900_);
        v___x_902_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_903_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7;
        leanh::lean_inc_n(v___x_901_, 10);
        v___x_904_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_904_, 0, v___x_901_);
        leanh::lean_ctor_set(v___x_904_, 1, v___x_903_);
        v___x_905_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9;
        v___x_906_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_907_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_908_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14;
        v___x_909_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_910_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_910_, 0, v___x_901_);
        leanh::lean_ctor_set(v___x_910_, 1, v___x_908_);
        v___x_911_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17), core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once), _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17);
        v___x_912_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22;
        leanh::lean_inc(v_currMacroScope_898_);
        leanh::lean_inc(v_quotContext_897_);
        v___x_913_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_912_, v_currMacroScope_898_);
        v___x_914_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24;
        v___x_915_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_915_, 0, v___x_901_);
        leanh::lean_ctor_set(v___x_915_, 1, v___x_911_);
        leanh::lean_ctor_set(v___x_915_, 2, v___x_913_);
        leanh::lean_ctor_set(v___x_915_, 3, v___x_914_);
        v___x_916_ = l_Lean_Syntax_node2(v___x_901_, v___x_909_, v___x_910_, v___x_915_);
        v___x_917_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_918_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_918_, 0, v___x_901_);
        leanh::lean_ctor_set(v___x_918_, 1, v___x_917_);
        v___x_919_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26;
        v___x_920_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_921_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_921_, 0, v___x_901_);
        leanh::lean_ctor_set(v___x_921_, 1, v___x_919_);
        v___x_922_ = l_Lean_Syntax_node1(v___x_901_, v___x_920_, v___x_921_);
        v___x_923_ =
            l_Lean_Syntax_node3(v___x_901_, v___x_907_, v___x_916_, v___x_918_, v___x_922_);
        v___x_924_ = l_Lean_Syntax_node1(v___x_901_, v___x_906_, v___x_923_);
        v___x_925_ = l_Lean_Syntax_node1(v___x_901_, v___x_905_, v___x_924_);
        v___x_926_ = l_Lean_Syntax_node2(v___x_901_, v___x_902_, v___x_904_, v___x_925_);
        v___x_927_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_927_, 0, v___x_926_);
        leanh::lean_ctor_set(v___x_927_, 1, v_a_892_);
        return v___x_927_;
    }
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___boxed(
    mut v_x_928_: *mut leanh::LeanObject,
    mut v_a_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(v_x_928_, v_a_929_, v_a_930_);
    leanh::lean_dec_ref(v_a_929_);
    return v_res_931_;
}
pub unsafe fn _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0;
    v___x_934_ = l_String_toRawSubstring_x27(v___x_933_);
    return v___x_934_;
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(
    mut v_x_947_: *mut leanh::LeanObject,
    mut v_a_948_: *mut leanh::LeanObject,
    mut v_a_949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: u8 = 0;
    v___x_950_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_951_ = l_Lean_Syntax_isOfKind(v_x_947_, v___x_950_);
    if v___x_951_ == 0 {
        let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_952_ = leanh::lean_box(1);
        v___x_953_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_953_, 0, v___x_952_);
        leanh::lean_ctor_set(v___x_953_, 1, v_a_949_);
        return v___x_953_;
    } else {
        let mut v_quotContext_954_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_957_: u8 = 0;
        let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_954_ = leanh::lean_ctor_get(v_a_948_, 1);
        v_currMacroScope_955_ = leanh::lean_ctor_get(v_a_948_, 2);
        v_ref_956_ = leanh::lean_ctor_get(v_a_948_, 5);
        v___x_957_ = 0;
        v___x_958_ = l_Lean_SourceInfo_fromRef(v_ref_956_, v___x_957_);
        v___x_959_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_960_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7;
        leanh::lean_inc_n(v___x_958_, 10);
        v___x_961_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_961_, 0, v___x_958_);
        leanh::lean_ctor_set(v___x_961_, 1, v___x_960_);
        v___x_962_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9;
        v___x_963_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_964_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_965_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14;
        v___x_966_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_967_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_967_, 0, v___x_958_);
        leanh::lean_ctor_set(v___x_967_, 1, v___x_965_);
        v___x_968_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1), core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once), _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1);
        v___x_969_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3;
        leanh::lean_inc(v_currMacroScope_955_);
        leanh::lean_inc(v_quotContext_954_);
        v___x_970_ = l_Lean_addMacroScope(v_quotContext_954_, v___x_969_, v_currMacroScope_955_);
        v___x_971_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5;
        v___x_972_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_972_, 0, v___x_958_);
        leanh::lean_ctor_set(v___x_972_, 1, v___x_968_);
        leanh::lean_ctor_set(v___x_972_, 2, v___x_970_);
        leanh::lean_ctor_set(v___x_972_, 3, v___x_971_);
        v___x_973_ = l_Lean_Syntax_node2(v___x_958_, v___x_966_, v___x_967_, v___x_972_);
        v___x_974_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_975_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_975_, 0, v___x_958_);
        leanh::lean_ctor_set(v___x_975_, 1, v___x_974_);
        v___x_976_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26;
        v___x_977_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_978_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_978_, 0, v___x_958_);
        leanh::lean_ctor_set(v___x_978_, 1, v___x_976_);
        v___x_979_ = l_Lean_Syntax_node1(v___x_958_, v___x_977_, v___x_978_);
        v___x_980_ =
            l_Lean_Syntax_node3(v___x_958_, v___x_964_, v___x_973_, v___x_975_, v___x_979_);
        v___x_981_ = l_Lean_Syntax_node1(v___x_958_, v___x_963_, v___x_980_);
        v___x_982_ = l_Lean_Syntax_node1(v___x_958_, v___x_962_, v___x_981_);
        v___x_983_ = l_Lean_Syntax_node2(v___x_958_, v___x_959_, v___x_961_, v___x_982_);
        v___x_984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_984_, 0, v___x_983_);
        leanh::lean_ctor_set(v___x_984_, 1, v_a_949_);
        return v___x_984_;
    }
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___boxed(
    mut v_x_985_: *mut leanh::LeanObject,
    mut v_a_986_: *mut leanh::LeanObject,
    mut v_a_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(v_x_985_, v_a_986_, v_a_987_);
    leanh::lean_dec_ref(v_a_986_);
    return v_res_988_;
}
pub unsafe fn l_String_Legacy_Iterator_setCurr(
    mut v_x_989_: *mut leanh::LeanObject,
    mut v_x_990_: u32,
) -> *mut leanh::LeanObject {
    let mut v_s_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_991_ = leanh::lean_ctor_get(v_x_989_, 0);
                v_i_992_ = leanh::lean_ctor_get(v_x_989_, 1);
                v_isSharedCheck_1000_ = (!leanh::lean_is_exclusive(v_x_989_)) as u8;
                if v_isSharedCheck_1000_ == 0 {
                    v___x_994_ = v_x_989_;
                    v_isShared_995_ = v_isSharedCheck_1000_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_i_992_);
                    leanh::lean_inc(v_s_991_);
                    leanh::lean_dec(v_x_989_);
                    v___x_994_ = leanh::lean_box(0);
                    v_isShared_995_ = v_isSharedCheck_1000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_996_ = lean_string_utf8_set(v_s_991_, v_i_992_, v_x_990_);
                if v_isShared_995_ == 0 {
                    leanh::lean_ctor_set(v___x_994_, 0, v___x_996_);
                    v___x_998_ = v___x_994_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_999_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_999_, 1, v_i_992_);
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
    mut v_x_1001_: *mut leanh::LeanObject,
    mut v_x_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_15__boxed_1003_: u32 = 0;
    let mut v_res_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_15__boxed_1003_ = leanh::lean_unbox_uint32(v_x_1002_);
    leanh::lean_dec(v_x_1002_);
    v_res_1004_ = l_String_Legacy_Iterator_setCurr(v_x_1001_, v_x_15__boxed_1003_);
    return v_res_1004_;
}
pub unsafe fn l_String_Legacy_Iterator_find(
    mut v_it_1005_: *mut leanh::LeanObject,
    mut v_p_1006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: u8 = 0;
    let mut v___x_1011_: u32 = 0;
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1017_: u8 = 0;
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1023_: u8 = 0;
    let mut v_unused_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1007_ = leanh::lean_ctor_get(v_it_1005_, 0);
                v_i_1008_ = leanh::lean_ctor_get(v_it_1005_, 1);
                v___x_1009_ = lean_string_utf8_byte_size(v_s_1007_);
                v___x_1010_ = lean_nat_dec_le(v___x_1009_, v_i_1008_);
                if v___x_1010_ == 0 {
                    v___x_1011_ = lean_string_utf8_get(v_s_1007_, v_i_1008_);
                    v___x_1012_ = leanh::lean_box_uint32(v___x_1011_);
                    leanh::lean_inc_ref(v_p_1006_);
                    v___x_1013_ = leanh::lean_apply_1(v_p_1006_, v___x_1012_);
                    v___x_1014_ = (leanh::lean_unbox(v___x_1013_) as u8);
                    if v___x_1014_ == 0 {
                        leanh::lean_inc(v_i_1008_);
                        leanh::lean_inc_ref(v_s_1007_);
                        v_isSharedCheck_1023_ =
                            (!leanh::lean_is_exclusive(v_it_1005_)) as u8;
                        if v_isSharedCheck_1023_ == 0 {
                            v_unused_1024_ = leanh::lean_ctor_get(v_it_1005_, 1);
                            leanh::lean_dec(v_unused_1024_);
                            v_unused_1025_ = leanh::lean_ctor_get(v_it_1005_, 0);
                            leanh::lean_dec(v_unused_1025_);
                            v___x_1016_ = v_it_1005_;
                            v_isShared_1017_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_it_1005_);
                            v___x_1016_ = leanh::lean_box(0);
                            v_isShared_1017_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_p_1006_);
                        return v_it_1005_;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_1006_);
                    return v_it_1005_;
                }
            }
            1 => {
                v___x_1018_ = lean_string_utf8_next(v_s_1007_, v_i_1008_);
                leanh::lean_dec(v_i_1008_);
                if v_isShared_1017_ == 0 {
                    leanh::lean_ctor_set(v___x_1016_, 1, v___x_1018_);
                    v___x_1020_ = v___x_1016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1022_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_s_1007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1018_);
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
    mut v_it_1026_: *mut leanh::LeanObject,
    mut v_init_1027_: *mut leanh::LeanObject,
    mut v_f_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: u32 = 0;
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v_val_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut v_unused_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1029_ = leanh::lean_ctor_get(v_it_1026_, 0);
                v_i_1030_ = leanh::lean_ctor_get(v_it_1026_, 1);
                v___x_1031_ = lean_string_utf8_byte_size(v_s_1029_);
                v___x_1032_ = lean_nat_dec_le(v___x_1031_, v_i_1030_);
                if v___x_1032_ == 0 {
                    v___x_1033_ = lean_string_utf8_get(v_s_1029_, v_i_1030_);
                    v___x_1034_ = leanh::lean_box_uint32(v___x_1033_);
                    leanh::lean_inc_ref(v_f_1028_);
                    leanh::lean_inc(v_init_1027_);
                    v___x_1035_ = leanh::lean_apply_2(v_f_1028_, v_init_1027_, v___x_1034_);
                    if leanh::lean_obj_tag(v___x_1035_) == 1 {
                        leanh::lean_inc(v_i_1030_);
                        leanh::lean_inc_ref(v_s_1029_);
                        leanh::lean_dec(v_init_1027_);
                        v_isSharedCheck_1045_ =
                            (!leanh::lean_is_exclusive(v_it_1026_)) as u8;
                        if v_isSharedCheck_1045_ == 0 {
                            v_unused_1046_ = leanh::lean_ctor_get(v_it_1026_, 1);
                            leanh::lean_dec(v_unused_1046_);
                            v_unused_1047_ = leanh::lean_ctor_get(v_it_1026_, 0);
                            leanh::lean_dec(v_unused_1047_);
                            v___x_1037_ = v_it_1026_;
                            v_isShared_1038_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_it_1026_);
                            v___x_1037_ = leanh::lean_box(0);
                            v_isShared_1038_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1035_);
                        leanh::lean_dec_ref(v_f_1028_);
                        v___x_1048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1048_, 0, v_init_1027_);
                        leanh::lean_ctor_set(v___x_1048_, 1, v_it_1026_);
                        return v___x_1048_;
                    }
                } else {
                    leanh::lean_dec_ref(v_f_1028_);
                    v___x_1049_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1049_, 0, v_init_1027_);
                    leanh::lean_ctor_set(v___x_1049_, 1, v_it_1026_);
                    return v___x_1049_;
                }
            }
            1 => {
                v_val_1039_ = leanh::lean_ctor_get(v___x_1035_, 0);
                leanh::lean_inc(v_val_1039_);
                leanh::lean_dec_ref_known(v___x_1035_, 1);
                v___x_1040_ = lean_string_utf8_next(v_s_1029_, v_i_1030_);
                leanh::lean_dec(v_i_1030_);
                if v_isShared_1038_ == 0 {
                    leanh::lean_ctor_set(v___x_1037_, 1, v___x_1040_);
                    v___x_1042_ = v___x_1037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1044_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_s_1029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1040_);
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
    mut v_00_u03b1_1050_: *mut leanh::LeanObject,
    mut v_it_1051_: *mut leanh::LeanObject,
    mut v_init_1052_: *mut leanh::LeanObject,
    mut v_f_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_String_Legacy_Iterator_foldUntil___redArg(v_it_1051_, v_init_1052_, v_f_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter___redArg(
    mut v_x_1055_: *mut leanh::LeanObject,
    mut v_h__1_1056_: *mut leanh::LeanObject,
    mut v_h__2_1057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1055_) == 1 {
        let mut v_val_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1057_);
        v_val_1058_ = leanh::lean_ctor_get(v_x_1055_, 0);
        leanh::lean_inc(v_val_1058_);
        leanh::lean_dec_ref_known(v_x_1055_, 1);
        v___x_1059_ = leanh::lean_apply_1(v_h__1_1056_, v_val_1058_);
        return v___x_1059_;
    } else {
        let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1056_);
        v___x_1060_ =
            leanh::lean_apply_2(v_h__2_1057_, v_x_1055_, leanh::lean_box(0));
        return v___x_1060_;
    }
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter(
    mut v_00_u03b1_1061_: *mut leanh::LeanObject,
    mut v_motive_1062_: *mut leanh::LeanObject,
    mut v_x_1063_: *mut leanh::LeanObject,
    mut v_h__1_1064_: *mut leanh::LeanObject,
    mut v_h__2_1065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1063_) == 1 {
        let mut v_val_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1065_);
        v_val_1066_ = leanh::lean_ctor_get(v_x_1063_, 0);
        leanh::lean_inc(v_val_1066_);
        leanh::lean_dec_ref_known(v_x_1063_, 1);
        v___x_1067_ = leanh::lean_apply_1(v_h__1_1064_, v_val_1066_);
        return v___x_1067_;
    } else {
        let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1064_);
        v___x_1068_ =
            leanh::lean_apply_2(v_h__2_1065_, v_x_1063_, leanh::lean_box(0));
        return v___x_1068_;
    }
}
pub unsafe fn l_Substring_Raw_toLegacyIterator(
    mut v_x_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_str_1070_ = leanh::lean_ctor_get(v_x_1069_, 0);
    v_startPos_1071_ = leanh::lean_ctor_get(v_x_1069_, 1);
    leanh::lean_inc(v_startPos_1071_);
    leanh::lean_inc_ref(v_str_1070_);
    v___x_1072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1072_, 0, v_str_1070_);
    leanh::lean_ctor_set(v___x_1072_, 1, v_startPos_1071_);
    return v___x_1072_;
}
pub unsafe fn l_Substring_Raw_toLegacyIterator___boxed(
    mut v_x_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Substring_Raw_toLegacyIterator(v_x_1073_);
    leanh::lean_dec_ref(v_x_1073_);
    return v_res_1074_;
}
pub unsafe fn l_instReprIterator___lam__0(
    mut v_x_1087_: *mut leanh::LeanObject,
    mut v_x_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1089_ = leanh::lean_ctor_get(v_x_1087_, 0);
                v_i_1090_ = leanh::lean_ctor_get(v_x_1087_, 1);
                v_isSharedCheck_1110_ = (!leanh::lean_is_exclusive(v_x_1087_)) as u8;
                if v_isSharedCheck_1110_ == 0 {
                    v___x_1092_ = v_x_1087_;
                    v_isShared_1093_ = v_isSharedCheck_1110_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_i_1090_);
                    leanh::lean_inc(v_s_1089_);
                    leanh::lean_dec(v_x_1087_);
                    v___x_1092_ = leanh::lean_box(0);
                    v_isShared_1093_ = v_isSharedCheck_1110_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1094_ = l_instReprIterator___lam__0___closed__1;
                v___x_1095_ = l_String_quote(v_s_1089_);
                v___x_1096_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1096_, 0, v___x_1095_);
                if v_isShared_1093_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1092_, 5);
                    leanh::lean_ctor_set(v___x_1092_, 1, v___x_1096_);
                    leanh::lean_ctor_set(v___x_1092_, 0, v___x_1094_);
                    v___x_1098_ = v___x_1092_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1109_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1096_);
                    v___x_1098_ = v_reuseFailAlloc_1109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1099_ = l_instReprIterator___lam__0___closed__3;
                v___x_1100_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1100_, 0, v___x_1098_);
                leanh::lean_ctor_set(v___x_1100_, 1, v___x_1099_);
                v___x_1101_ = l_instReprIterator___lam__0___closed__5;
                v___x_1102_ = l_Nat_reprFast(v_i_1090_);
                v___x_1103_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1103_, 0, v___x_1102_);
                v___x_1104_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1104_, 0, v___x_1101_);
                leanh::lean_ctor_set(v___x_1104_, 1, v___x_1103_);
                v___x_1105_ = l_instReprIterator___lam__0___closed__7;
                v___x_1106_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1106_, 0, v___x_1104_);
                leanh::lean_ctor_set(v___x_1106_, 1, v___x_1105_);
                v___x_1107_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1107_, 0, v___x_1100_);
                leanh::lean_ctor_set(v___x_1107_, 1, v___x_1106_);
                v___x_1108_ = l_Repr_addAppParen(v___x_1107_, v_x_1088_);
                return v___x_1108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instReprIterator___lam__0___boxed(
    mut v_x_1111_: *mut leanh::LeanObject,
    mut v_x_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_instReprIterator___lam__0(v_x_1111_, v_x_1112_);
    leanh::lean_dec(v_x_1112_);
    return v_res_1113_;
}
pub unsafe fn l_instToStringIterator___lam__0(
    mut v_it_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_1117_ = leanh::lean_ctor_get(v_it_1116_, 0);
    v_i_1118_ = leanh::lean_ctor_get(v_it_1116_, 1);
    v___x_1119_ = lean_string_utf8_byte_size(v_s_1117_);
    v___x_1120_ = lean_string_utf8_extract(v_s_1117_, v_i_1118_, v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn l_instToStringIterator___lam__0___boxed(
    mut v_it_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_instToStringIterator___lam__0(v_it_1121_);
    leanh::lean_dec_ref(v_it_1121_);
    return v_res_1122_;
}
pub unsafe fn l_String_iter(
    mut v_s_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = leanh::lean_unsigned_to_nat(0);
    v___x_1127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1127_, 0, v_s_1125_);
    leanh::lean_ctor_set(v___x_1127_, 1, v___x_1126_);
    return v___x_1127_;
}
pub unsafe fn l_String_mkIterator(
    mut v_s_1128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = leanh::lean_unsigned_to_nat(0);
    v___x_1130_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1130_, 0, v_s_1128_);
    leanh::lean_ctor_set(v___x_1130_, 1, v___x_1129_);
    return v___x_1130_;
}
pub unsafe fn l_String_Iterator_curr(mut v_a_1131_: *mut leanh::LeanObject) -> u32 {
    let mut v_s_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: u32 = 0;
    v_s_1132_ = leanh::lean_ctor_get(v_a_1131_, 0);
    v_i_1133_ = leanh::lean_ctor_get(v_a_1131_, 1);
    v___x_1134_ = lean_string_utf8_get(v_s_1132_, v_i_1133_);
    return v___x_1134_;
}
pub unsafe fn l_String_Iterator_curr___boxed(
    mut v_a_1135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1136_: u32 = 0;
    let mut v_r_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1136_ = l_String_Iterator_curr(v_a_1135_);
    leanh::lean_dec_ref(v_a_1135_);
    v_r_1137_ = leanh::lean_box_uint32(v_res_1136_);
    return v_r_1137_;
}
pub unsafe fn l_String_Iterator_next(
    mut v_a_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1139_ = leanh::lean_ctor_get(v_a_1138_, 0);
                v_i_1140_ = leanh::lean_ctor_get(v_a_1138_, 1);
                v_isSharedCheck_1148_ = (!leanh::lean_is_exclusive(v_a_1138_)) as u8;
                if v_isSharedCheck_1148_ == 0 {
                    v___x_1142_ = v_a_1138_;
                    v_isShared_1143_ = v_isSharedCheck_1148_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_i_1140_);
                    leanh::lean_inc(v_s_1139_);
                    leanh::lean_dec(v_a_1138_);
                    v___x_1142_ = leanh::lean_box(0);
                    v_isShared_1143_ = v_isSharedCheck_1148_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1144_ = lean_string_utf8_next(v_s_1139_, v_i_1140_);
                leanh::lean_dec(v_i_1140_);
                if v_isShared_1143_ == 0 {
                    leanh::lean_ctor_set(v___x_1142_, 1, v___x_1144_);
                    v___x_1146_ = v___x_1142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1147_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_s_1139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1144_);
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
pub unsafe fn l_String_Iterator_hasNext(mut v_a_1149_: *mut leanh::LeanObject) -> u8 {
    let mut v_s_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    v_s_1150_ = leanh::lean_ctor_get(v_a_1149_, 0);
    v_i_1151_ = leanh::lean_ctor_get(v_a_1149_, 1);
    v___x_1152_ = lean_string_utf8_byte_size(v_s_1150_);
    v___x_1153_ = lean_nat_dec_lt(v_i_1151_, v___x_1152_);
    return v___x_1153_;
}
pub unsafe fn l_String_Iterator_hasNext___boxed(
    mut v_a_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1155_: u8 = 0;
    let mut v_r_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_String_Iterator_hasNext(v_a_1154_);
    leanh::lean_dec_ref(v_a_1154_);
    v_r_1156_ = leanh::lean_box((v_res_1155_) as usize);
    return v_r_1156_;
}
pub unsafe fn l_Substring_toIterator(
    mut v_a_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_str_1158_ = leanh::lean_ctor_get(v_a_1157_, 0);
    v_startPos_1159_ = leanh::lean_ctor_get(v_a_1157_, 1);
    leanh::lean_inc(v_startPos_1159_);
    leanh::lean_inc_ref(v_str_1158_);
    v___x_1160_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1160_, 0, v_str_1158_);
    leanh::lean_ctor_set(v___x_1160_, 1, v_startPos_1159_);
    return v___x_1160_;
}
pub unsafe fn l_Substring_toIterator___boxed(
    mut v_a_1161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Substring_toIterator(v_a_1161_);
    leanh::lean_dec_ref(v_a_1161_);
    return v_res_1162_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Iterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Iterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Iterator(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Iterator(builtin);
}