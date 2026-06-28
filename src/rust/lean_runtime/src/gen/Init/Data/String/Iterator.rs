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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_box_uint32, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l_String_Legacy_instInhabitedIterator_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_String_Legacy_instInhabitedIterator_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__0_value)
        as *mut LeanObject;
pub static l_String_Legacy_instInhabitedIterator_default___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_String_Legacy_instInhabitedIterator_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_String_Legacy_instInhabitedIterator_default: *mut LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_String_Legacy_instInhabitedIterator: *mut LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instInhabitedIterator_default___closed__1_value)
        as *mut LeanObject;
pub static l_String_Legacy_instSizeOfIterator___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_String_Legacy_instSizeOfIterator___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_Legacy_instSizeOfIterator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instSizeOfIterator___closed__0_value) as *mut LeanObject;
pub static mut l_String_Legacy_instSizeOfIterator: *mut LeanObject =
    core::ptr::addr_of!(l_String_Legacy_instSizeOfIterator___closed__0_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114, 105, 118, 105, 97, 108, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut LeanObject,5744670087858236374 as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut LeanObject,6022092293134036165 as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value) as *mut LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__8_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut LeanObject,5826123769708379594 as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16_value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [83, 116, 114, 105, 110, 103, 46, 76, 101, 103, 97, 99, 121, 46, 73, 116, 101, 114, 97, 116, 111, 114, 46, 115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 104, 97, 115, 78, 101, 120, 116, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16_value) as *mut LeanObject;
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 105, 110, 103, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 101, 103, 97, 99, 121, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 116, 101, 114, 97, 116, 111, 114, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 104, 97, 115, 78, 101, 120, 116, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value) as *mut LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut LeanObject,16221383843924677366 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut LeanObject,13785796134284214332 as *mut LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__21_value) as *mut LeanObject,17921308319265575761 as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut LeanObject,16687334436616221424 as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0_value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [83, 116, 114, 105, 110, 103, 46, 76, 101, 103, 97, 99, 121, 46, 73, 116, 101, 114, 97, 116, 111, 114, 46, 115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 97, 116, 69, 110, 100, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0_value) as *mut LeanObject;
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [115, 105, 122, 101, 79, 102, 95, 110, 101, 120, 116, 95, 108, 116, 95, 111, 102, 95, 97, 116, 69, 110, 100, 0]};
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut LeanObject;
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut LeanObject,16221383843924677366 as *mut LeanObject] };
static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut LeanObject,13785796134284214332 as *mut LeanObject] };
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut LeanObject,4155438117962710745 as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut LeanObject;
pub static l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5: *mut LeanObject = core::ptr::addr_of!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5_value) as *mut LeanObject;
pub static l_instReprIterator___lam__0___closed__0_value: LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 114, 105, 110, 103, 46, 73, 116, 101, 114, 97, 116, 111, 114, 46, 109, 107, 32, 0,
    ],
};
static mut l_instReprIterator___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__0_value) as *mut LeanObject;
pub static l_instReprIterator___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_instReprIterator___lam__0___closed__0_value) as *mut LeanObject],
};
static mut l_instReprIterator___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__1_value) as *mut LeanObject;
pub static l_instReprIterator___lam__0___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_instReprIterator___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__2_value) as *mut LeanObject;
pub static l_instReprIterator___lam__0___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_instReprIterator___lam__0___closed__2_value) as *mut LeanObject],
};
static mut l_instReprIterator___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__3_value) as *mut LeanObject;
pub static l_instReprIterator___lam__0___closed__4_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_instReprIterator___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__4_value) as *mut LeanObject;
pub static l_instReprIterator___lam__0___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_instReprIterator___lam__0___closed__4_value) as *mut LeanObject],
};
static mut l_instReprIterator___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__5_value) as *mut LeanObject;
pub static l_instReprIterator___lam__0___closed__6_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_instReprIterator___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__6_value) as *mut LeanObject;
pub static l_instReprIterator___lam__0___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_instReprIterator___lam__0___closed__6_value) as *mut LeanObject],
};
static mut l_instReprIterator___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___lam__0___closed__7_value) as *mut LeanObject;
pub static l_instReprIterator___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprIterator___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instReprIterator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___closed__0_value) as *mut LeanObject;
pub static mut l_instReprIterator: *mut LeanObject =
    core::ptr::addr_of!(l_instReprIterator___closed__0_value) as *mut LeanObject;
pub static l_instToStringIterator___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringIterator___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringIterator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringIterator___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringIterator: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringIterator___closed__0_value) as *mut LeanObject;
pub unsafe fn l_String_Legacy_instDecidableEqIterator_decEq(
    mut v_x_582_: *mut LeanObject,
    mut v_x_583_: *mut LeanObject,
) -> u8 {
    let mut v_s_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    v_s_584_ = lean_ctor_get(v_x_582_, 0);
    v_i_585_ = lean_ctor_get(v_x_582_, 1);
    v_s_586_ = lean_ctor_get(v_x_583_, 0);
    v_i_587_ = lean_ctor_get(v_x_583_, 1);
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
    mut v_x_590_: *mut LeanObject,
    mut v_x_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_592_: u8 = 0;
    let mut v_r_593_: *mut LeanObject = core::ptr::null_mut();
    v_res_592_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_590_, v_x_591_);
    lean_dec_ref(v_x_591_);
    lean_dec_ref(v_x_590_);
    v_r_593_ = lean_box((v_res_592_) as usize);
    return v_r_593_;
}
pub unsafe fn l_String_Legacy_instDecidableEqIterator(
    mut v_x_594_: *mut LeanObject,
    mut v_x_595_: *mut LeanObject,
) -> u8 {
    let mut v___x_596_: u8 = 0;
    v___x_596_ = l_String_Legacy_instDecidableEqIterator_decEq(v_x_594_, v_x_595_);
    return v___x_596_;
}
pub unsafe fn l_String_Legacy_instDecidableEqIterator___boxed(
    mut v_x_597_: *mut LeanObject,
    mut v_x_598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_599_: u8 = 0;
    let mut v_r_600_: *mut LeanObject = core::ptr::null_mut();
    v_res_599_ = l_String_Legacy_instDecidableEqIterator(v_x_597_, v_x_598_);
    lean_dec_ref(v_x_598_);
    lean_dec_ref(v_x_597_);
    v_r_600_ = lean_box((v_res_599_) as usize);
    return v_r_600_;
}
pub unsafe fn l_String_Legacy_mkIterator(mut v_s_607_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ = lean_unsigned_to_nat(0);
    v___x_609_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_609_, 0, v_s_607_);
    lean_ctor_set(v___x_609_, 1, v___x_608_);
    return v___x_609_;
}
pub unsafe fn l_String_Legacy_iter(mut v_s_610_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    v___x_611_ = lean_unsigned_to_nat(0);
    v___x_612_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_612_, 0, v_s_610_);
    lean_ctor_set(v___x_612_, 1, v___x_611_);
    return v___x_612_;
}
pub unsafe fn l_String_Legacy_instSizeOfIterator___lam__0(
    mut v_i_613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    v_s_614_ = lean_ctor_get(v_i_613_, 0);
    v_i_615_ = lean_ctor_get(v_i_613_, 1);
    v___x_616_ = lean_string_utf8_byte_size(v_s_614_);
    v___x_617_ = lean_nat_sub(v___x_616_, v_i_615_);
    return v___x_617_;
}
pub unsafe fn l_String_Legacy_instSizeOfIterator___lam__0___boxed(
    mut v_i_618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_619_: *mut LeanObject = core::ptr::null_mut();
    v_res_619_ = l_String_Legacy_instSizeOfIterator___lam__0(v_i_618_);
    lean_dec_ref(v_i_618_);
    return v_res_619_;
}
pub unsafe fn l_String_Legacy_Iterator_toString(
    mut v_self_622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_623_: *mut LeanObject = core::ptr::null_mut();
    v_s_623_ = lean_ctor_get(v_self_622_, 0);
    lean_inc_ref(v_s_623_);
    return v_s_623_;
}
pub unsafe fn l_String_Legacy_Iterator_toString___boxed(
    mut v_self_624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_625_: *mut LeanObject = core::ptr::null_mut();
    v_res_625_ = l_String_Legacy_Iterator_toString(v_self_624_);
    lean_dec_ref(v_self_624_);
    return v_res_625_;
}
pub unsafe fn l_String_Legacy_Iterator_remainingBytes(
    mut v_x_626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v_s_627_ = lean_ctor_get(v_x_626_, 0);
    v_i_628_ = lean_ctor_get(v_x_626_, 1);
    v___x_629_ = lean_string_utf8_byte_size(v_s_627_);
    v___x_630_ = lean_nat_sub(v___x_629_, v_i_628_);
    return v___x_630_;
}
pub unsafe fn l_String_Legacy_Iterator_remainingBytes___boxed(
    mut v_x_631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_632_: *mut LeanObject = core::ptr::null_mut();
    v_res_632_ = l_String_Legacy_Iterator_remainingBytes(v_x_631_);
    lean_dec_ref(v_x_631_);
    return v_res_632_;
}
pub unsafe fn l_String_Legacy_Iterator_pos(mut v_self_633_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_634_: *mut LeanObject = core::ptr::null_mut();
    v_i_634_ = lean_ctor_get(v_self_633_, 1);
    lean_inc(v_i_634_);
    return v_i_634_;
}
pub unsafe fn l_String_Legacy_Iterator_pos___boxed(
    mut v_self_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_636_: *mut LeanObject = core::ptr::null_mut();
    v_res_636_ = l_String_Legacy_Iterator_pos(v_self_635_);
    lean_dec_ref(v_self_635_);
    return v_res_636_;
}
pub unsafe fn l_String_Legacy_Iterator_curr(mut v_x_637_: *mut LeanObject) -> u32 {
    let mut v_s_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: u32 = 0;
    v_s_638_ = lean_ctor_get(v_x_637_, 0);
    v_i_639_ = lean_ctor_get(v_x_637_, 1);
    v___x_640_ = lean_string_utf8_get(v_s_638_, v_i_639_);
    return v___x_640_;
}
pub unsafe fn l_String_Legacy_Iterator_curr___boxed(
    mut v_x_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_642_: u32 = 0;
    let mut v_r_643_: *mut LeanObject = core::ptr::null_mut();
    v_res_642_ = l_String_Legacy_Iterator_curr(v_x_641_);
    lean_dec_ref(v_x_641_);
    v_r_643_ = lean_box_uint32(v_res_642_);
    return v_r_643_;
}
pub unsafe fn l_String_Legacy_Iterator_next(mut v_x_644_: *mut LeanObject) -> *mut LeanObject {
    let mut v_s_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_645_ = lean_ctor_get(v_x_644_, 0);
                v_i_646_ = lean_ctor_get(v_x_644_, 1);
                v_isSharedCheck_654_ = (!lean_is_exclusive(v_x_644_)) as u8;
                if v_isSharedCheck_654_ == 0 {
                    v___x_648_ = v_x_644_;
                    v_isShared_649_ = v_isSharedCheck_654_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_i_646_);
                    lean_inc(v_s_645_);
                    lean_dec(v_x_644_);
                    v___x_648_ = lean_box(0);
                    v_isShared_649_ = v_isSharedCheck_654_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_650_ = lean_string_utf8_next(v_s_645_, v_i_646_);
                lean_dec(v_i_646_);
                if v_isShared_649_ == 0 {
                    lean_ctor_set(v___x_648_, 1, v___x_650_);
                    v___x_652_ = v___x_648_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_653_, 0, v_s_645_);
                    lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
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
pub unsafe fn l_String_Legacy_Iterator_prev(mut v_x_655_: *mut LeanObject) -> *mut LeanObject {
    let mut v_s_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_656_ = lean_ctor_get(v_x_655_, 0);
                v_i_657_ = lean_ctor_get(v_x_655_, 1);
                v_isSharedCheck_665_ = (!lean_is_exclusive(v_x_655_)) as u8;
                if v_isSharedCheck_665_ == 0 {
                    v___x_659_ = v_x_655_;
                    v_isShared_660_ = v_isSharedCheck_665_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_i_657_);
                    lean_inc(v_s_656_);
                    lean_dec(v_x_655_);
                    v___x_659_ = lean_box(0);
                    v_isShared_660_ = v_isSharedCheck_665_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_661_ = lean_string_utf8_prev(v_s_656_, v_i_657_);
                lean_dec(v_i_657_);
                if v_isShared_660_ == 0 {
                    lean_ctor_set(v___x_659_, 1, v___x_661_);
                    v___x_663_ = v___x_659_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_664_, 0, v_s_656_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
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
pub unsafe fn l_String_Legacy_Iterator_atEnd(mut v_x_666_: *mut LeanObject) -> u8 {
    let mut v_s_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: u8 = 0;
    v_s_667_ = lean_ctor_get(v_x_666_, 0);
    v_i_668_ = lean_ctor_get(v_x_666_, 1);
    v___x_669_ = lean_string_utf8_byte_size(v_s_667_);
    v___x_670_ = lean_nat_dec_le(v___x_669_, v_i_668_);
    return v___x_670_;
}
pub unsafe fn l_String_Legacy_Iterator_atEnd___boxed(
    mut v_x_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_672_: u8 = 0;
    let mut v_r_673_: *mut LeanObject = core::ptr::null_mut();
    v_res_672_ = l_String_Legacy_Iterator_atEnd(v_x_671_);
    lean_dec_ref(v_x_671_);
    v_r_673_ = lean_box((v_res_672_) as usize);
    return v_r_673_;
}
pub unsafe fn l_String_Legacy_Iterator_hasNext(mut v_x_674_: *mut LeanObject) -> u8 {
    let mut v_s_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u8 = 0;
    v_s_675_ = lean_ctor_get(v_x_674_, 0);
    v_i_676_ = lean_ctor_get(v_x_674_, 1);
    v___x_677_ = lean_string_utf8_byte_size(v_s_675_);
    v___x_678_ = lean_nat_dec_lt(v_i_676_, v___x_677_);
    return v___x_678_;
}
pub unsafe fn l_String_Legacy_Iterator_hasNext___boxed(
    mut v_x_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_680_: u8 = 0;
    let mut v_r_681_: *mut LeanObject = core::ptr::null_mut();
    v_res_680_ = l_String_Legacy_Iterator_hasNext(v_x_679_);
    lean_dec_ref(v_x_679_);
    v_r_681_ = lean_box((v_res_680_) as usize);
    return v_r_681_;
}
pub unsafe fn l_String_Legacy_Iterator_hasPrev(mut v_x_682_: *mut LeanObject) -> u8 {
    let mut v_i_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    v_i_683_ = lean_ctor_get(v_x_682_, 1);
    v___x_684_ = lean_unsigned_to_nat(0);
    v___x_685_ = lean_nat_dec_lt(v___x_684_, v_i_683_);
    return v___x_685_;
}
pub unsafe fn l_String_Legacy_Iterator_hasPrev___boxed(
    mut v_x_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_687_: u8 = 0;
    let mut v_r_688_: *mut LeanObject = core::ptr::null_mut();
    v_res_687_ = l_String_Legacy_Iterator_hasPrev(v_x_686_);
    lean_dec_ref(v_x_686_);
    v_r_688_ = lean_box((v_res_687_) as usize);
    return v_r_688_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter___redArg(
    mut v_x_689_: *mut LeanObject,
    mut v_h__1_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    v_s_691_ = lean_ctor_get(v_x_689_, 0);
    lean_inc_ref(v_s_691_);
    v_i_692_ = lean_ctor_get(v_x_689_, 1);
    lean_inc(v_i_692_);
    lean_dec_ref(v_x_689_);
    v___x_693_ = lean_apply_2(v_h__1_690_, v_s_691_, v_i_692_);
    return v___x_693_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_remainingBytes_match__1_splitter(
    mut v_motive_694_: *mut LeanObject,
    mut v_x_695_: *mut LeanObject,
    mut v_h__1_696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    v_s_697_ = lean_ctor_get(v_x_695_, 0);
    lean_inc_ref(v_s_697_);
    v_i_698_ = lean_ctor_get(v_x_695_, 1);
    lean_inc(v_i_698_);
    lean_dec_ref(v_x_695_);
    v___x_699_ = lean_apply_2(v_h__1_696_, v_s_697_, v_i_698_);
    return v___x_699_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(
    mut v_x_700_: *mut LeanObject,
    mut v_x_701_: *mut LeanObject,
    mut v_h__1_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    v___x_703_ = lean_apply_2(v_h__1_702_, v_x_700_, v_x_701_);
    return v___x_703_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Pos_Raw_get_x3f_match__1_splitter(
    mut v_motive_704_: *mut LeanObject,
    mut v_x_705_: *mut LeanObject,
    mut v_x_706_: *mut LeanObject,
    mut v_h__1_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___x_708_ = lean_apply_2(v_h__1_707_, v_x_705_, v_x_706_);
    return v___x_708_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27___redArg(mut v_it_709_: *mut LeanObject) -> u32 {
    let mut v_s_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u32 = 0;
    v_s_710_ = lean_ctor_get(v_it_709_, 0);
    v_i_711_ = lean_ctor_get(v_it_709_, 1);
    v___x_712_ = lean_string_utf8_get_fast(v_s_710_, v_i_711_);
    return v___x_712_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27___redArg___boxed(
    mut v_it_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_714_: u32 = 0;
    let mut v_r_715_: *mut LeanObject = core::ptr::null_mut();
    v_res_714_ = l_String_Legacy_Iterator_curr_x27___redArg(v_it_713_);
    lean_dec_ref(v_it_713_);
    v_r_715_ = lean_box_uint32(v_res_714_);
    return v_r_715_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27(
    mut v_it_716_: *mut LeanObject,
    mut v_h_717_: *mut LeanObject,
) -> u32 {
    let mut v_s_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u32 = 0;
    v_s_718_ = lean_ctor_get(v_it_716_, 0);
    v_i_719_ = lean_ctor_get(v_it_716_, 1);
    v___x_720_ = lean_string_utf8_get_fast(v_s_718_, v_i_719_);
    return v___x_720_;
}
pub unsafe fn l_String_Legacy_Iterator_curr_x27___boxed(
    mut v_it_721_: *mut LeanObject,
    mut v_h_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_723_: u32 = 0;
    let mut v_r_724_: *mut LeanObject = core::ptr::null_mut();
    v_res_723_ = l_String_Legacy_Iterator_curr_x27(v_it_721_, v_h_722_);
    lean_dec_ref(v_it_721_);
    v_r_724_ = lean_box_uint32(v_res_723_);
    return v_r_724_;
}
pub unsafe fn l_String_Legacy_Iterator_next_x27___redArg(
    mut v_it_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_726_ = lean_ctor_get(v_it_725_, 0);
                v_i_727_ = lean_ctor_get(v_it_725_, 1);
                v_isSharedCheck_735_ = (!lean_is_exclusive(v_it_725_)) as u8;
                if v_isSharedCheck_735_ == 0 {
                    v___x_729_ = v_it_725_;
                    v_isShared_730_ = v_isSharedCheck_735_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_i_727_);
                    lean_inc(v_s_726_);
                    lean_dec(v_it_725_);
                    v___x_729_ = lean_box(0);
                    v_isShared_730_ = v_isSharedCheck_735_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_731_ = lean_string_utf8_next_fast(v_s_726_, v_i_727_);
                lean_dec(v_i_727_);
                if v_isShared_730_ == 0 {
                    lean_ctor_set(v___x_729_, 1, v___x_731_);
                    v___x_733_ = v___x_729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_734_, 0, v_s_726_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_731_);
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
    mut v_it_736_: *mut LeanObject,
    mut v_h_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_738_ = lean_ctor_get(v_it_736_, 0);
                v_i_739_ = lean_ctor_get(v_it_736_, 1);
                v_isSharedCheck_747_ = (!lean_is_exclusive(v_it_736_)) as u8;
                if v_isSharedCheck_747_ == 0 {
                    v___x_741_ = v_it_736_;
                    v_isShared_742_ = v_isSharedCheck_747_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_i_739_);
                    lean_inc(v_s_738_);
                    lean_dec(v_it_736_);
                    v___x_741_ = lean_box(0);
                    v_isShared_742_ = v_isSharedCheck_747_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_743_ = lean_string_utf8_next_fast(v_s_738_, v_i_739_);
                lean_dec(v_i_739_);
                if v_isShared_742_ == 0 {
                    lean_ctor_set(v___x_741_, 1, v___x_743_);
                    v___x_745_ = v___x_741_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_746_, 0, v_s_738_);
                    lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_743_);
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
pub unsafe fn l_String_Legacy_Iterator_toEnd(mut v_x_748_: *mut LeanObject) -> *mut LeanObject {
    let mut v_s_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_752_: u8 = 0;
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_757_: u8 = 0;
    let mut v_unused_758_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_749_ = lean_ctor_get(v_x_748_, 0);
                v_isSharedCheck_757_ = (!lean_is_exclusive(v_x_748_)) as u8;
                if v_isSharedCheck_757_ == 0 {
                    v_unused_758_ = lean_ctor_get(v_x_748_, 1);
                    lean_dec(v_unused_758_);
                    v___x_751_ = v_x_748_;
                    v_isShared_752_ = v_isSharedCheck_757_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_s_749_);
                    lean_dec(v_x_748_);
                    v___x_751_ = lean_box(0);
                    v_isShared_752_ = v_isSharedCheck_757_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_753_ = lean_string_utf8_byte_size(v_s_749_);
                if v_isShared_752_ == 0 {
                    lean_ctor_set(v___x_751_, 1, v___x_753_);
                    v___x_755_ = v___x_751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_756_, 0, v_s_749_);
                    lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
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
    mut v_x_759_: *mut LeanObject,
    mut v_x_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: u8 = 0;
    v_s_761_ = lean_ctor_get(v_x_759_, 0);
    v_i_762_ = lean_ctor_get(v_x_759_, 1);
    v_s_763_ = lean_ctor_get(v_x_760_, 0);
    v_i_764_ = lean_ctor_get(v_x_760_, 1);
    v___x_765_ = lean_string_dec_eq(v_s_761_, v_s_763_);
    if v___x_765_ == 0 {
        let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
        v___x_766_ = l_String_Legacy_instInhabitedIterator_default___closed__0;
        return v___x_766_;
    } else {
        let mut v___x_767_: u8 = 0;
        v___x_767_ = lean_nat_dec_lt(v_i_764_, v_i_762_);
        if v___x_767_ == 0 {
            let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
            v___x_768_ = lean_string_utf8_extract(v_s_761_, v_i_762_, v_i_764_);
            return v___x_768_;
        } else {
            let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
            v___x_769_ = l_String_Legacy_instInhabitedIterator_default___closed__0;
            return v___x_769_;
        }
    }
}
pub unsafe fn l_String_Legacy_Iterator_extract___boxed(
    mut v_x_770_: *mut LeanObject,
    mut v_x_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_772_: *mut LeanObject = core::ptr::null_mut();
    v_res_772_ = l_String_Legacy_Iterator_extract(v_x_770_, v_x_771_);
    lean_dec_ref(v_x_771_);
    lean_dec_ref(v_x_770_);
    return v_res_772_;
}
pub unsafe fn l_String_Legacy_Iterator_forward(
    mut v_x_773_: *mut LeanObject,
    mut v_x_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_776_: u8 = 0;
    let mut v_s_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_781_: u8 = 0;
    let mut v_one_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_775_ = lean_unsigned_to_nat(0);
                v_isZero_776_ = lean_nat_dec_eq(v_x_774_, v_zero_775_);
                if v_isZero_776_ == 1 {
                    lean_dec(v_x_774_);
                    return v_x_773_;
                } else {
                    v_s_777_ = lean_ctor_get(v_x_773_, 0);
                    v_i_778_ = lean_ctor_get(v_x_773_, 1);
                    v_isSharedCheck_789_ = (!lean_is_exclusive(v_x_773_)) as u8;
                    if v_isSharedCheck_789_ == 0 {
                        v___x_780_ = v_x_773_;
                        v_isShared_781_ = v_isSharedCheck_789_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_i_778_);
                        lean_inc(v_s_777_);
                        lean_dec(v_x_773_);
                        v___x_780_ = lean_box(0);
                        v_isShared_781_ = v_isSharedCheck_789_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_782_ = lean_unsigned_to_nat(1);
                v_n_783_ = lean_nat_sub(v_x_774_, v_one_782_);
                lean_dec(v_x_774_);
                v___x_784_ = lean_string_utf8_next(v_s_777_, v_i_778_);
                lean_dec(v_i_778_);
                if v_isShared_781_ == 0 {
                    lean_ctor_set(v___x_780_, 1, v___x_784_);
                    v___x_786_ = v___x_780_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_788_, 0, v_s_777_);
                    lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_784_);
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
    mut v_x_790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    v_s_791_ = lean_ctor_get(v_x_790_, 0);
    v_i_792_ = lean_ctor_get(v_x_790_, 1);
    v___x_793_ = lean_string_utf8_byte_size(v_s_791_);
    v___x_794_ = lean_string_utf8_extract(v_s_791_, v_i_792_, v___x_793_);
    return v___x_794_;
}
pub unsafe fn l_String_Legacy_Iterator_remainingToString___boxed(
    mut v_x_795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_796_: *mut LeanObject = core::ptr::null_mut();
    v_res_796_ = l_String_Legacy_Iterator_remainingToString(v_x_795_);
    lean_dec_ref(v_x_795_);
    return v_res_796_;
}
pub unsafe fn l_String_Legacy_Iterator_nextn(
    mut v_x_797_: *mut LeanObject,
    mut v_x_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_800_: u8 = 0;
    let mut v_s_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v_one_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_799_ = lean_unsigned_to_nat(0);
                v_isZero_800_ = lean_nat_dec_eq(v_x_798_, v_zero_799_);
                if v_isZero_800_ == 1 {
                    lean_dec(v_x_798_);
                    return v_x_797_;
                } else {
                    v_s_801_ = lean_ctor_get(v_x_797_, 0);
                    v_i_802_ = lean_ctor_get(v_x_797_, 1);
                    v_isSharedCheck_813_ = (!lean_is_exclusive(v_x_797_)) as u8;
                    if v_isSharedCheck_813_ == 0 {
                        v___x_804_ = v_x_797_;
                        v_isShared_805_ = v_isSharedCheck_813_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_i_802_);
                        lean_inc(v_s_801_);
                        lean_dec(v_x_797_);
                        v___x_804_ = lean_box(0);
                        v_isShared_805_ = v_isSharedCheck_813_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_806_ = lean_unsigned_to_nat(1);
                v_n_807_ = lean_nat_sub(v_x_798_, v_one_806_);
                lean_dec(v_x_798_);
                v___x_808_ = lean_string_utf8_next(v_s_801_, v_i_802_);
                lean_dec(v_i_802_);
                if v_isShared_805_ == 0 {
                    lean_ctor_set(v___x_804_, 1, v___x_808_);
                    v___x_810_ = v___x_804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_812_, 0, v_s_801_);
                    lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_808_);
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
    mut v_x_814_: *mut LeanObject,
    mut v_x_815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_817_: u8 = 0;
    let mut v_s_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v_one_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_816_ = lean_unsigned_to_nat(0);
                v_isZero_817_ = lean_nat_dec_eq(v_x_815_, v_zero_816_);
                if v_isZero_817_ == 1 {
                    lean_dec(v_x_815_);
                    return v_x_814_;
                } else {
                    v_s_818_ = lean_ctor_get(v_x_814_, 0);
                    v_i_819_ = lean_ctor_get(v_x_814_, 1);
                    v_isSharedCheck_830_ = (!lean_is_exclusive(v_x_814_)) as u8;
                    if v_isSharedCheck_830_ == 0 {
                        v___x_821_ = v_x_814_;
                        v_isShared_822_ = v_isSharedCheck_830_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_i_819_);
                        lean_inc(v_s_818_);
                        lean_dec(v_x_814_);
                        v___x_821_ = lean_box(0);
                        v_isShared_822_ = v_isSharedCheck_830_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_one_823_ = lean_unsigned_to_nat(1);
                v_n_824_ = lean_nat_sub(v_x_815_, v_one_823_);
                lean_dec(v_x_815_);
                v___x_825_ = lean_string_utf8_prev(v_s_818_, v_i_819_);
                lean_dec(v_i_819_);
                if v_isShared_822_ == 0 {
                    lean_ctor_set(v___x_821_, 1, v___x_825_);
                    v___x_827_ = v___x_821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_829_, 0, v_s_818_);
                    lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_825_);
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
-> *mut LeanObject {
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    v___x_866_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__16;
    v___x_867_ = l_String_toRawSubstring_x27(v___x_866_);
    return v___x_867_;
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(
    mut v_x_890_: *mut LeanObject,
    mut v_a_891_: *mut LeanObject,
    mut v_a_892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: u8 = 0;
    v___x_893_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_894_ = l_Lean_Syntax_isOfKind(v_x_890_, v___x_893_);
    if v___x_894_ == 0 {
        let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
        v___x_895_ = lean_box(1);
        v___x_896_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_896_, 0, v___x_895_);
        lean_ctor_set(v___x_896_, 1, v_a_892_);
        return v___x_896_;
    } else {
        let mut v_quotContext_897_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_898_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_900_: u8 = 0;
        let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_897_ = lean_ctor_get(v_a_891_, 1);
        v_currMacroScope_898_ = lean_ctor_get(v_a_891_, 2);
        v_ref_899_ = lean_ctor_get(v_a_891_, 5);
        v___x_900_ = 0;
        v___x_901_ = l_Lean_SourceInfo_fromRef(v_ref_899_, v___x_900_);
        v___x_902_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_903_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7;
        lean_inc_n(v___x_901_, 10);
        v___x_904_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_904_, 0, v___x_901_);
        lean_ctor_set(v___x_904_, 1, v___x_903_);
        v___x_905_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9;
        v___x_906_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_907_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_908_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14;
        v___x_909_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_910_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_910_, 0, v___x_901_);
        lean_ctor_set(v___x_910_, 1, v___x_908_);
        v___x_911_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17), core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17_once), _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__17);
        v___x_912_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__22;
        lean_inc(v_currMacroScope_898_);
        lean_inc(v_quotContext_897_);
        v___x_913_ = l_Lean_addMacroScope(v_quotContext_897_, v___x_912_, v_currMacroScope_898_);
        v___x_914_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__24;
        v___x_915_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_915_, 0, v___x_901_);
        lean_ctor_set(v___x_915_, 1, v___x_911_);
        lean_ctor_set(v___x_915_, 2, v___x_913_);
        lean_ctor_set(v___x_915_, 3, v___x_914_);
        v___x_916_ = l_Lean_Syntax_node2(v___x_901_, v___x_909_, v___x_910_, v___x_915_);
        v___x_917_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_918_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_918_, 0, v___x_901_);
        lean_ctor_set(v___x_918_, 1, v___x_917_);
        v___x_919_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26;
        v___x_920_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_921_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_921_, 0, v___x_901_);
        lean_ctor_set(v___x_921_, 1, v___x_919_);
        v___x_922_ = l_Lean_Syntax_node1(v___x_901_, v___x_920_, v___x_921_);
        v___x_923_ =
            l_Lean_Syntax_node3(v___x_901_, v___x_907_, v___x_916_, v___x_918_, v___x_922_);
        v___x_924_ = l_Lean_Syntax_node1(v___x_901_, v___x_906_, v___x_923_);
        v___x_925_ = l_Lean_Syntax_node1(v___x_901_, v___x_905_, v___x_924_);
        v___x_926_ = l_Lean_Syntax_node2(v___x_901_, v___x_902_, v___x_904_, v___x_925_);
        v___x_927_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_927_, 0, v___x_926_);
        lean_ctor_set(v___x_927_, 1, v_a_892_);
        return v___x_927_;
    }
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___boxed(
    mut v_x_928_: *mut LeanObject,
    mut v_a_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_931_: *mut LeanObject = core::ptr::null_mut();
    v_res_931_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1(v_x_928_, v_a_929_, v_a_930_);
    lean_dec_ref(v_a_929_);
    return v_res_931_;
}
pub unsafe fn _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1()
-> *mut LeanObject {
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    v___x_933_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__0;
    v___x_934_ = l_String_toRawSubstring_x27(v___x_933_);
    return v___x_934_;
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(
    mut v_x_947_: *mut LeanObject,
    mut v_a_948_: *mut LeanObject,
    mut v_a_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: u8 = 0;
    v___x_950_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_951_ = l_Lean_Syntax_isOfKind(v_x_947_, v___x_950_);
    if v___x_951_ == 0 {
        let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
        v___x_952_ = lean_box(1);
        v___x_953_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_953_, 0, v___x_952_);
        lean_ctor_set(v___x_953_, 1, v_a_949_);
        return v___x_953_;
    } else {
        let mut v_quotContext_954_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_955_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_957_: u8 = 0;
        let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_954_ = lean_ctor_get(v_a_948_, 1);
        v_currMacroScope_955_ = lean_ctor_get(v_a_948_, 2);
        v_ref_956_ = lean_ctor_get(v_a_948_, 5);
        v___x_957_ = 0;
        v___x_958_ = l_Lean_SourceInfo_fromRef(v_ref_956_, v___x_957_);
        v___x_959_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_960_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__7;
        lean_inc_n(v___x_958_, 10);
        v___x_961_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_961_, 0, v___x_958_);
        lean_ctor_set(v___x_961_, 1, v___x_960_);
        v___x_962_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__9;
        v___x_963_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_964_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_965_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__14;
        v___x_966_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_967_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_967_, 0, v___x_958_);
        lean_ctor_set(v___x_967_, 1, v___x_965_);
        v___x_968_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1), core::ptr::addr_of_mut!(l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1_once), _init_l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__1);
        v___x_969_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__3;
        lean_inc(v_currMacroScope_955_);
        lean_inc(v_quotContext_954_);
        v___x_970_ = l_Lean_addMacroScope(v_quotContext_954_, v___x_969_, v_currMacroScope_955_);
        v___x_971_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___closed__5;
        v___x_972_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_972_, 0, v___x_958_);
        lean_ctor_set(v___x_972_, 1, v___x_968_);
        lean_ctor_set(v___x_972_, 2, v___x_970_);
        lean_ctor_set(v___x_972_, 3, v___x_971_);
        v___x_973_ = l_Lean_Syntax_node2(v___x_958_, v___x_966_, v___x_967_, v___x_972_);
        v___x_974_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_975_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_975_, 0, v___x_958_);
        lean_ctor_set(v___x_975_, 1, v___x_974_);
        v___x_976_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__26;
        v___x_977_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_978_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_978_, 0, v___x_958_);
        lean_ctor_set(v___x_978_, 1, v___x_976_);
        v___x_979_ = l_Lean_Syntax_node1(v___x_958_, v___x_977_, v___x_978_);
        v___x_980_ =
            l_Lean_Syntax_node3(v___x_958_, v___x_964_, v___x_973_, v___x_975_, v___x_979_);
        v___x_981_ = l_Lean_Syntax_node1(v___x_958_, v___x_963_, v___x_980_);
        v___x_982_ = l_Lean_Syntax_node1(v___x_958_, v___x_962_, v___x_981_);
        v___x_983_ = l_Lean_Syntax_node2(v___x_958_, v___x_959_, v___x_961_, v___x_982_);
        v___x_984_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_984_, 0, v___x_983_);
        lean_ctor_set(v___x_984_, 1, v_a_949_);
        return v___x_984_;
    }
}
pub unsafe fn l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2___boxed(
    mut v_x_985_: *mut LeanObject,
    mut v_a_986_: *mut LeanObject,
    mut v_a_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_988_: *mut LeanObject = core::ptr::null_mut();
    v_res_988_ = l_String_Legacy_Iterator___aux__Init__Data__String__Iterator______macroRules__tacticDecreasing__trivial__2(v_x_985_, v_a_986_, v_a_987_);
    lean_dec_ref(v_a_986_);
    return v_res_988_;
}
pub unsafe fn l_String_Legacy_Iterator_setCurr(
    mut v_x_989_: *mut LeanObject,
    mut v_x_990_: u32,
) -> *mut LeanObject {
    let mut v_s_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_991_ = lean_ctor_get(v_x_989_, 0);
                v_i_992_ = lean_ctor_get(v_x_989_, 1);
                v_isSharedCheck_1000_ = (!lean_is_exclusive(v_x_989_)) as u8;
                if v_isSharedCheck_1000_ == 0 {
                    v___x_994_ = v_x_989_;
                    v_isShared_995_ = v_isSharedCheck_1000_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_i_992_);
                    lean_inc(v_s_991_);
                    lean_dec(v_x_989_);
                    v___x_994_ = lean_box(0);
                    v_isShared_995_ = v_isSharedCheck_1000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_996_ = lean_string_utf8_set(v_s_991_, v_i_992_, v_x_990_);
                if v_isShared_995_ == 0 {
                    lean_ctor_set(v___x_994_, 0, v___x_996_);
                    v___x_998_ = v___x_994_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
                    lean_ctor_set(v_reuseFailAlloc_999_, 1, v_i_992_);
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
    mut v_x_1001_: *mut LeanObject,
    mut v_x_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_15__boxed_1003_: u32 = 0;
    let mut v_res_1004_: *mut LeanObject = core::ptr::null_mut();
    v_x_15__boxed_1003_ = lean_unbox_uint32(v_x_1002_);
    lean_dec(v_x_1002_);
    v_res_1004_ = l_String_Legacy_Iterator_setCurr(v_x_1001_, v_x_15__boxed_1003_);
    return v_res_1004_;
}
pub unsafe fn l_String_Legacy_Iterator_find(
    mut v_it_1005_: *mut LeanObject,
    mut v_p_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: u8 = 0;
    let mut v___x_1011_: u32 = 0;
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1017_: u8 = 0;
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1023_: u8 = 0;
    let mut v_unused_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1007_ = lean_ctor_get(v_it_1005_, 0);
                v_i_1008_ = lean_ctor_get(v_it_1005_, 1);
                v___x_1009_ = lean_string_utf8_byte_size(v_s_1007_);
                v___x_1010_ = lean_nat_dec_le(v___x_1009_, v_i_1008_);
                if v___x_1010_ == 0 {
                    v___x_1011_ = lean_string_utf8_get(v_s_1007_, v_i_1008_);
                    v___x_1012_ = lean_box_uint32(v___x_1011_);
                    lean_inc_ref(v_p_1006_);
                    v___x_1013_ = lean_apply_1(v_p_1006_, v___x_1012_);
                    v___x_1014_ = (lean_unbox(v___x_1013_) as u8);
                    if v___x_1014_ == 0 {
                        lean_inc(v_i_1008_);
                        lean_inc_ref(v_s_1007_);
                        v_isSharedCheck_1023_ = (!lean_is_exclusive(v_it_1005_)) as u8;
                        if v_isSharedCheck_1023_ == 0 {
                            v_unused_1024_ = lean_ctor_get(v_it_1005_, 1);
                            lean_dec(v_unused_1024_);
                            v_unused_1025_ = lean_ctor_get(v_it_1005_, 0);
                            lean_dec(v_unused_1025_);
                            v___x_1016_ = v_it_1005_;
                            v_isShared_1017_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_it_1005_);
                            v___x_1016_ = lean_box(0);
                            v_isShared_1017_ = v_isSharedCheck_1023_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_p_1006_);
                        return v_it_1005_;
                    }
                } else {
                    lean_dec_ref(v_p_1006_);
                    return v_it_1005_;
                }
            }
            1 => {
                v___x_1018_ = lean_string_utf8_next(v_s_1007_, v_i_1008_);
                lean_dec(v_i_1008_);
                if v_isShared_1017_ == 0 {
                    lean_ctor_set(v___x_1016_, 1, v___x_1018_);
                    v___x_1020_ = v___x_1016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_s_1007_);
                    lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1018_);
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
    mut v_it_1026_: *mut LeanObject,
    mut v_init_1027_: *mut LeanObject,
    mut v_f_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: u32 = 0;
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v_val_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut v_unused_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1029_ = lean_ctor_get(v_it_1026_, 0);
                v_i_1030_ = lean_ctor_get(v_it_1026_, 1);
                v___x_1031_ = lean_string_utf8_byte_size(v_s_1029_);
                v___x_1032_ = lean_nat_dec_le(v___x_1031_, v_i_1030_);
                if v___x_1032_ == 0 {
                    v___x_1033_ = lean_string_utf8_get(v_s_1029_, v_i_1030_);
                    v___x_1034_ = lean_box_uint32(v___x_1033_);
                    lean_inc_ref(v_f_1028_);
                    lean_inc(v_init_1027_);
                    v___x_1035_ = lean_apply_2(v_f_1028_, v_init_1027_, v___x_1034_);
                    if lean_obj_tag(v___x_1035_) == 1 {
                        lean_inc(v_i_1030_);
                        lean_inc_ref(v_s_1029_);
                        lean_dec(v_init_1027_);
                        v_isSharedCheck_1045_ = (!lean_is_exclusive(v_it_1026_)) as u8;
                        if v_isSharedCheck_1045_ == 0 {
                            v_unused_1046_ = lean_ctor_get(v_it_1026_, 1);
                            lean_dec(v_unused_1046_);
                            v_unused_1047_ = lean_ctor_get(v_it_1026_, 0);
                            lean_dec(v_unused_1047_);
                            v___x_1037_ = v_it_1026_;
                            v_isShared_1038_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_it_1026_);
                            v___x_1037_ = lean_box(0);
                            v_isShared_1038_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1035_);
                        lean_dec_ref(v_f_1028_);
                        v___x_1048_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1048_, 0, v_init_1027_);
                        lean_ctor_set(v___x_1048_, 1, v_it_1026_);
                        return v___x_1048_;
                    }
                } else {
                    lean_dec_ref(v_f_1028_);
                    v___x_1049_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1049_, 0, v_init_1027_);
                    lean_ctor_set(v___x_1049_, 1, v_it_1026_);
                    return v___x_1049_;
                }
            }
            1 => {
                v_val_1039_ = lean_ctor_get(v___x_1035_, 0);
                lean_inc(v_val_1039_);
                lean_dec_ref_known(v___x_1035_, 1);
                v___x_1040_ = lean_string_utf8_next(v_s_1029_, v_i_1030_);
                lean_dec(v_i_1030_);
                if v_isShared_1038_ == 0 {
                    lean_ctor_set(v___x_1037_, 1, v___x_1040_);
                    v___x_1042_ = v___x_1037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_s_1029_);
                    lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1040_);
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
    mut v_00_u03b1_1050_: *mut LeanObject,
    mut v_it_1051_: *mut LeanObject,
    mut v_init_1052_: *mut LeanObject,
    mut v_f_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_String_Legacy_Iterator_foldUntil___redArg(v_it_1051_, v_init_1052_, v_f_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter___redArg(
    mut v_x_1055_: *mut LeanObject,
    mut v_h__1_1056_: *mut LeanObject,
    mut v_h__2_1057_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1055_) == 1 {
        let mut v_val_1058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1057_);
        v_val_1058_ = lean_ctor_get(v_x_1055_, 0);
        lean_inc(v_val_1058_);
        lean_dec_ref_known(v_x_1055_, 1);
        v___x_1059_ = lean_apply_1(v_h__1_1056_, v_val_1058_);
        return v___x_1059_;
    } else {
        let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1056_);
        v___x_1060_ = lean_apply_2(v_h__2_1057_, v_x_1055_, lean_box(0));
        return v___x_1060_;
    }
}
pub unsafe fn l___private_Init_Data_String_Iterator_0__String_Legacy_Iterator_foldUntil_match__1_splitter(
    mut v_00_u03b1_1061_: *mut LeanObject,
    mut v_motive_1062_: *mut LeanObject,
    mut v_x_1063_: *mut LeanObject,
    mut v_h__1_1064_: *mut LeanObject,
    mut v_h__2_1065_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1063_) == 1 {
        let mut v_val_1066_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1065_);
        v_val_1066_ = lean_ctor_get(v_x_1063_, 0);
        lean_inc(v_val_1066_);
        lean_dec_ref_known(v_x_1063_, 1);
        v___x_1067_ = lean_apply_1(v_h__1_1064_, v_val_1066_);
        return v___x_1067_;
    } else {
        let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1064_);
        v___x_1068_ = lean_apply_2(v_h__2_1065_, v_x_1063_, lean_box(0));
        return v___x_1068_;
    }
}
pub unsafe fn l_Substring_Raw_toLegacyIterator(mut v_x_1069_: *mut LeanObject) -> *mut LeanObject {
    let mut v_str_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startPos_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    v_str_1070_ = lean_ctor_get(v_x_1069_, 0);
    v_startPos_1071_ = lean_ctor_get(v_x_1069_, 1);
    lean_inc(v_startPos_1071_);
    lean_inc_ref(v_str_1070_);
    v___x_1072_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1072_, 0, v_str_1070_);
    lean_ctor_set(v___x_1072_, 1, v_startPos_1071_);
    return v___x_1072_;
}
pub unsafe fn l_Substring_Raw_toLegacyIterator___boxed(
    mut v_x_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Substring_Raw_toLegacyIterator(v_x_1073_);
    lean_dec_ref(v_x_1073_);
    return v_res_1074_;
}
pub unsafe fn l_instReprIterator___lam__0(
    mut v_x_1087_: *mut LeanObject,
    mut v_x_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1089_ = lean_ctor_get(v_x_1087_, 0);
                v_i_1090_ = lean_ctor_get(v_x_1087_, 1);
                v_isSharedCheck_1110_ = (!lean_is_exclusive(v_x_1087_)) as u8;
                if v_isSharedCheck_1110_ == 0 {
                    v___x_1092_ = v_x_1087_;
                    v_isShared_1093_ = v_isSharedCheck_1110_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_i_1090_);
                    lean_inc(v_s_1089_);
                    lean_dec(v_x_1087_);
                    v___x_1092_ = lean_box(0);
                    v_isShared_1093_ = v_isSharedCheck_1110_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1094_ = l_instReprIterator___lam__0___closed__1;
                v___x_1095_ = l_String_quote(v_s_1089_);
                v___x_1096_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1096_, 0, v___x_1095_);
                if v_isShared_1093_ == 0 {
                    lean_ctor_set_tag(v___x_1092_, 5);
                    lean_ctor_set(v___x_1092_, 1, v___x_1096_);
                    lean_ctor_set(v___x_1092_, 0, v___x_1094_);
                    v___x_1098_ = v___x_1092_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1109_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1094_);
                    lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1096_);
                    v___x_1098_ = v_reuseFailAlloc_1109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1099_ = l_instReprIterator___lam__0___closed__3;
                v___x_1100_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1100_, 0, v___x_1098_);
                lean_ctor_set(v___x_1100_, 1, v___x_1099_);
                v___x_1101_ = l_instReprIterator___lam__0___closed__5;
                v___x_1102_ = l_Nat_reprFast(v_i_1090_);
                v___x_1103_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1103_, 0, v___x_1102_);
                v___x_1104_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1104_, 0, v___x_1101_);
                lean_ctor_set(v___x_1104_, 1, v___x_1103_);
                v___x_1105_ = l_instReprIterator___lam__0___closed__7;
                v___x_1106_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1106_, 0, v___x_1104_);
                lean_ctor_set(v___x_1106_, 1, v___x_1105_);
                v___x_1107_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1107_, 0, v___x_1100_);
                lean_ctor_set(v___x_1107_, 1, v___x_1106_);
                v___x_1108_ = l_Repr_addAppParen(v___x_1107_, v_x_1088_);
                return v___x_1108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instReprIterator___lam__0___boxed(
    mut v_x_1111_: *mut LeanObject,
    mut v_x_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1113_: *mut LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_instReprIterator___lam__0(v_x_1111_, v_x_1112_);
    lean_dec(v_x_1112_);
    return v_res_1113_;
}
pub unsafe fn l_instToStringIterator___lam__0(mut v_it_1116_: *mut LeanObject) -> *mut LeanObject {
    let mut v_s_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v_s_1117_ = lean_ctor_get(v_it_1116_, 0);
    v_i_1118_ = lean_ctor_get(v_it_1116_, 1);
    v___x_1119_ = lean_string_utf8_byte_size(v_s_1117_);
    v___x_1120_ = lean_string_utf8_extract(v_s_1117_, v_i_1118_, v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn l_instToStringIterator___lam__0___boxed(
    mut v_it_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1122_: *mut LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_instToStringIterator___lam__0(v_it_1121_);
    lean_dec_ref(v_it_1121_);
    return v_res_1122_;
}
pub unsafe fn l_String_iter(mut v_s_1125_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    v___x_1126_ = lean_unsigned_to_nat(0);
    v___x_1127_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1127_, 0, v_s_1125_);
    lean_ctor_set(v___x_1127_, 1, v___x_1126_);
    return v___x_1127_;
}
pub unsafe fn l_String_mkIterator(mut v_s_1128_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    v___x_1129_ = lean_unsigned_to_nat(0);
    v___x_1130_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1130_, 0, v_s_1128_);
    lean_ctor_set(v___x_1130_, 1, v___x_1129_);
    return v___x_1130_;
}
pub unsafe fn l_String_Iterator_curr(mut v_a_1131_: *mut LeanObject) -> u32 {
    let mut v_s_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: u32 = 0;
    v_s_1132_ = lean_ctor_get(v_a_1131_, 0);
    v_i_1133_ = lean_ctor_get(v_a_1131_, 1);
    v___x_1134_ = lean_string_utf8_get(v_s_1132_, v_i_1133_);
    return v___x_1134_;
}
pub unsafe fn l_String_Iterator_curr___boxed(mut v_a_1135_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1136_: u32 = 0;
    let mut v_r_1137_: *mut LeanObject = core::ptr::null_mut();
    v_res_1136_ = l_String_Iterator_curr(v_a_1135_);
    lean_dec_ref(v_a_1135_);
    v_r_1137_ = lean_box_uint32(v_res_1136_);
    return v_r_1137_;
}
pub unsafe fn l_String_Iterator_next(mut v_a_1138_: *mut LeanObject) -> *mut LeanObject {
    let mut v_s_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1139_ = lean_ctor_get(v_a_1138_, 0);
                v_i_1140_ = lean_ctor_get(v_a_1138_, 1);
                v_isSharedCheck_1148_ = (!lean_is_exclusive(v_a_1138_)) as u8;
                if v_isSharedCheck_1148_ == 0 {
                    v___x_1142_ = v_a_1138_;
                    v_isShared_1143_ = v_isSharedCheck_1148_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_i_1140_);
                    lean_inc(v_s_1139_);
                    lean_dec(v_a_1138_);
                    v___x_1142_ = lean_box(0);
                    v_isShared_1143_ = v_isSharedCheck_1148_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1144_ = lean_string_utf8_next(v_s_1139_, v_i_1140_);
                lean_dec(v_i_1140_);
                if v_isShared_1143_ == 0 {
                    lean_ctor_set(v___x_1142_, 1, v___x_1144_);
                    v___x_1146_ = v___x_1142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_s_1139_);
                    lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1144_);
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
pub unsafe fn l_String_Iterator_hasNext(mut v_a_1149_: *mut LeanObject) -> u8 {
    let mut v_s_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    v_s_1150_ = lean_ctor_get(v_a_1149_, 0);
    v_i_1151_ = lean_ctor_get(v_a_1149_, 1);
    v___x_1152_ = lean_string_utf8_byte_size(v_s_1150_);
    v___x_1153_ = lean_nat_dec_lt(v_i_1151_, v___x_1152_);
    return v___x_1153_;
}
pub unsafe fn l_String_Iterator_hasNext___boxed(mut v_a_1154_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1155_: u8 = 0;
    let mut v_r_1156_: *mut LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_String_Iterator_hasNext(v_a_1154_);
    lean_dec_ref(v_a_1154_);
    v_r_1156_ = lean_box((v_res_1155_) as usize);
    return v_r_1156_;
}
pub unsafe fn l_Substring_toIterator(mut v_a_1157_: *mut LeanObject) -> *mut LeanObject {
    let mut v_str_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startPos_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    v_str_1158_ = lean_ctor_get(v_a_1157_, 0);
    v_startPos_1159_ = lean_ctor_get(v_a_1157_, 1);
    lean_inc(v_startPos_1159_);
    lean_inc_ref(v_str_1158_);
    v___x_1160_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1160_, 0, v_str_1158_);
    lean_ctor_set(v___x_1160_, 1, v_startPos_1159_);
    return v___x_1160_;
}
pub unsafe fn l_Substring_toIterator___boxed(mut v_a_1161_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1162_: *mut LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Substring_toIterator(v_a_1161_);
    lean_dec_ref(v_a_1161_);
    return v_res_1162_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Iterator(builtin);
}
