// Lean compiler output
// Module: Lean.Parser.StrInterpolation
// Imports: Lean.Parser.Basic
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Parser::Basic::{
    initialize_Lean_Parser_Basic, l_Lean_Parser_andthenFn, l_Lean_Parser_isQuotableCharDefault,
    l_Lean_Parser_mkAntiquot, l_Lean_Parser_mkAtomicInfo, l_Lean_Parser_mkNodeToken,
    l_Lean_Parser_quotedCharCoreFn___boxed, l_Lean_Parser_withAntiquot,
    l_Lean_Parser_withoutPosition, runtime_initialize_Lean_Parser_Basic,
};
use crate::r#gen::Lean::Parser::Types::{
    l_Lean_Parser_InputContext_atEnd, l_Lean_Parser_ParserState_mkEOIError,
    l_Lean_Parser_ParserState_mkError, l_Lean_Parser_ParserState_mkNode,
    l_Lean_Parser_ParserState_next, l_Lean_Parser_ParserState_setPos,
    l_Lean_Parser_ParserState_stackSize, l_Lean_Parser_instBEqError_beq,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_get, lean_string_utf8_next,
};
use crate::lean_imports_rs::Init::Prelude::lean_uint32_dec_eq;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 76, 105, 116, 75, 105, 110, 100, 0]};
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__0_value) as *mut crate::leanh::LeanObject,3105859046792672728 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [39, 125, 39, 0]};
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__3_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__3_value) as *mut crate::leanh::LeanObject,14298422259736409839 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_isQuotableCharForStrInterpolant___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__6_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_quotedCharCoreFn___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__5_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__7_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [117, 110, 116, 101, 114, 109, 105, 110, 97, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 0]};
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_interpolatedStrFn___closed__0_value: crate::leanh::LeanStringObject<20> =
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
            105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 32, 115, 116, 114, 105, 110,
            103, 0,
        ],
    };
static mut l_Lean_Parser_interpolatedStrFn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_interpolatedStrFn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_interpolatedStrNoAntiquot___closed__0_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
    ],
};
static mut l_Lean_Parser_interpolatedStrNoAntiquot___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_interpolatedStrNoAntiquot___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_interpolatedStrNoAntiquot___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_interpolatedStrNoAntiquot___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_interpolatedStr___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_interpolatedStr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_interpolatedStrNoAntiquot___closed__0_value) as *mut crate::leanh::LeanObject,2797157559945049776 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3_value: crate::leanh::LeanStringObject<841> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 841, m_capacity: 841, m_length: 840, m_data: [84, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 40, 112, 41, 96, 32, 112, 97, 114, 115, 101, 115, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 32, 108, 105, 107, 101, 32, 96, 34, 102, 111, 111, 34, 96, 32, 40, 115, 101, 101, 32, 96, 115, 116, 114, 96, 41, 44, 32, 98, 117, 116, 32, 116, 104, 101, 32, 115, 116, 114, 105, 110, 103, 10, 109, 97, 121, 32, 97, 108, 115, 111, 32, 99, 111, 110, 116, 97, 105, 110, 32, 96, 123, 125, 96, 32, 101, 115, 99, 97, 112, 101, 115, 44, 32, 97, 110, 100, 32, 119, 105, 116, 104, 105, 110, 32, 116, 104, 101, 32, 101, 115, 99, 97, 112, 101, 115, 32, 116, 104, 101, 32, 112, 97, 114, 115, 101, 114, 32, 96, 112, 96, 32, 105, 115, 32, 117, 115, 101, 100, 46, 32, 70, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 44, 10, 96, 105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 40, 116, 101, 114, 109, 41, 96, 32, 119, 105, 108, 108, 32, 112, 97, 114, 115, 101, 32, 96, 34, 102, 111, 111, 32, 123, 50, 32, 43, 32, 50, 125, 34, 96, 44, 32, 119, 104, 101, 114, 101, 32, 96, 50, 32, 43, 32, 50, 96, 32, 105, 115, 32, 112, 97, 114, 115, 101, 100, 32, 97, 115, 32, 97, 32, 116, 101, 114, 109, 32, 114, 97, 116, 104, 101, 114, 32, 116, 104, 97, 110, 10, 97, 115, 32, 97, 32, 115, 116, 114, 105, 110, 103, 46, 32, 78, 111, 116, 101, 32, 116, 104, 97, 116, 32, 116, 104, 101, 32, 102, 117, 108, 108, 32, 76, 101, 97, 110, 32, 116, 101, 114, 109, 32, 103, 114, 97, 109, 109, 97, 114, 32, 105, 115, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 104, 101, 114, 101, 44, 32, 105, 110, 99, 108, 117, 100, 105, 110, 103, 32, 115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 115, 44, 10, 115, 111, 32, 102, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 32, 96, 34, 102, 111, 111, 32, 123, 34, 98, 97, 114, 34, 32, 43, 43, 32, 34, 98, 97, 122, 34, 125, 34, 96, 32, 105, 115, 32, 97, 32, 108, 101, 103, 97, 108, 32, 105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 40, 119, 104, 105, 99, 104, 32, 101, 118, 97, 108, 117, 97, 116, 101, 115, 32, 116, 111, 10, 96, 102, 111, 111, 32, 98, 97, 114, 98, 97, 122, 96, 41, 46, 10, 10, 84, 104, 105, 115, 32, 112, 97, 114, 115, 101, 114, 32, 104, 97, 115, 32, 97, 114, 105, 116, 121, 32, 49, 44, 32, 97, 110, 100, 32, 114, 101, 116, 117, 114, 110, 115, 32, 97, 32, 96, 105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100, 96, 32, 119, 105, 116, 104, 32, 97, 110, 32, 111, 100, 100, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 44, 10, 97, 108, 116, 101, 114, 110, 97, 116, 105, 110, 103, 32, 98, 101, 116, 119, 101, 101, 110, 32, 99, 104, 117, 110, 107, 115, 32, 111, 102, 32, 108, 105, 116, 101, 114, 97, 108, 32, 116, 101, 120, 116, 32, 97, 110, 100, 32, 114, 101, 115, 117, 108, 116, 115, 32, 102, 114, 111, 109, 32, 96, 112, 96, 46, 32, 84, 104, 101, 32, 108, 105, 116, 101, 114, 97, 108, 32, 99, 104, 117, 110, 107, 115, 32, 99, 111, 110, 116, 97, 105, 110, 10, 117, 110, 105, 110, 116, 101, 114, 112, 114, 101, 116, 101, 100, 32, 115, 117, 98, 115, 116, 114, 105, 110, 103, 115, 32, 111, 102, 32, 116, 104, 101, 32, 105, 110, 112, 117, 116, 46, 32, 70, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 44, 32, 96, 34, 102, 111, 111, 92, 110, 123, 50, 32, 43, 32, 50, 125, 34, 96, 32, 119, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 116, 104, 114, 101, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 58, 10, 97, 110, 32, 97, 116, 111, 109, 32, 96, 34, 102, 111, 111, 92, 110, 123, 96, 44, 32, 116, 104, 101, 32, 112, 97, 114, 115, 101, 100, 32, 96, 50, 32, 43, 32, 50, 96, 32, 116, 101, 114, 109, 44, 32, 97, 110, 100, 32, 116, 104, 101, 110, 32, 116, 104, 101, 32, 97, 116, 111, 109, 32, 96, 125, 34, 96, 46, 32, 0]};
static mut l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Parser_isQuotableCharForStrInterpolant(mut v_c_152_: u32) -> u8 {
    let mut v___x_153_: u32 = 0;
    let mut v___x_154_: u8 = 0;
    v___x_153_ = 123;
    v___x_154_ = lean_uint32_dec_eq(v_c_152_, v___x_153_);
    if v___x_154_ == 0 {
        let mut v___x_155_: u8 = 0;
        v___x_155_ = l_Lean_Parser_isQuotableCharDefault(v_c_152_);
        return v___x_155_;
    } else {
        return v___x_154_;
    }
}
pub unsafe fn l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(
    mut v_c_156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_157_: u32 = 0;
    let mut v_res_158_: u8 = 0;
    let mut v_r_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_157_ = crate::leanh::lean_unbox_uint32(v_c_156_);
    crate::leanh::lean_dec(v_c_156_);
    v_res_158_ = l_Lean_Parser_isQuotableCharForStrInterpolant(v_c_boxed_157_);
    v_r_159_ = crate::leanh::lean_box((v_res_158_) as usize);
    return v_r_159_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(
    mut v_x_160_: *mut crate::leanh::LeanObject,
    mut v_x_161_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_160_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_161_) == 0 {
            let mut v___x_162_: u8 = 0;
            v___x_162_ = 1;
            return v___x_162_;
        } else {
            let mut v___x_163_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_161_, 1);
            v___x_163_ = 0;
            return v___x_163_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_161_) == 0 {
            let mut v___x_164_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_160_, 1);
            v___x_164_ = 0;
            return v___x_164_;
        } else {
            let mut v_val_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_167_: u8 = 0;
            v_val_165_ = crate::leanh::lean_ctor_get(v_x_160_, 0);
            crate::leanh::lean_inc(v_val_165_);
            crate::leanh::lean_dec_ref_known(v_x_160_, 1);
            v_val_166_ = crate::leanh::lean_ctor_get(v_x_161_, 0);
            crate::leanh::lean_inc(v_val_166_);
            crate::leanh::lean_dec_ref_known(v_x_161_, 1);
            v___x_167_ = l_Lean_Parser_instBEqError_beq(v_val_165_, v_val_166_);
            return v___x_167_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0___boxed(
    mut v_x_168_: *mut crate::leanh::LeanObject,
    mut v_x_169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_170_: u8 = 0;
    let mut v_r_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_170_ = l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(v_x_168_, v_x_169_);
    v_r_171_ = crate::leanh::lean_box((v_res_170_) as usize);
    return v_r_171_;
}
pub unsafe fn l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse(
    mut v_p_185_: *mut crate::leanh::LeanObject,
    mut v_stackSize_186_: *mut crate::leanh::LeanObject,
    mut v_startPos_187_: *mut crate::leanh::LeanObject,
    mut v_c_188_: *mut crate::leanh::LeanObject,
    mut v_s_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: u8 = 0;
    let mut v_inputString_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: u8 = 0;
    let mut v_curr_195_: u32 = 0;
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: u32 = 0;
    let mut v___x_199_: u8 = 0;
    let mut v___x_200_: u32 = 0;
    let mut v___x_201_: u8 = 0;
    let mut v___x_202_: u32 = 0;
    let mut v___x_203_: u8 = 0;
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_211_: u8 = 0;
    let mut v_curr_212_: u32 = 0;
    let mut v___x_213_: u32 = 0;
    let mut v___x_214_: u8 = 0;
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: u8 = 0;
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_190_ = crate::leanh::lean_ctor_get(v_s_189_, 2);
                v_toInputContext_191_ = crate::leanh::lean_ctor_get(v_c_188_, 0);
                v___x_192_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_191_, v_pos_190_);
                if v___x_192_ == 0 {
                    v_inputString_193_ = crate::leanh::lean_ctor_get(v_toInputContext_191_, 0);
                    v___x_194_ = 1;
                    v_curr_195_ = lean_string_utf8_get(v_inputString_193_, v_pos_190_);
                    v___x_196_ = lean_string_utf8_next(v_inputString_193_, v_pos_190_);
                    v_s_197_ = l_Lean_Parser_ParserState_setPos(v_s_189_, v___x_196_);
                    v___x_198_ = 34;
                    v___x_199_ = lean_uint32_dec_eq(v_curr_195_, v___x_198_);
                    if v___x_199_ == 0 {
                        v___x_200_ = 92;
                        v___x_201_ = lean_uint32_dec_eq(v_curr_195_, v___x_200_);
                        if v___x_201_ == 0 {
                            v___x_202_ = 123;
                            v___x_203_ = lean_uint32_dec_eq(v_curr_195_, v___x_202_);
                            if v___x_203_ == 0 {
                                v_s_189_ = v_s_197_;
                                state = 0;
                                continue;
                            } else {
                                v___x_205_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1;
                                crate::leanh::lean_inc_ref_n(v_c_188_, 2);
                                v_s_206_ = l_Lean_Parser_mkNodeToken(
                                    v___x_205_,
                                    v_startPos_187_,
                                    v___x_194_,
                                    v_c_188_,
                                    v_s_197_,
                                );
                                crate::leanh::lean_inc_ref(v_p_185_);
                                v_s_207_ = crate::leanh::lean_apply_2(v_p_185_, v_c_188_, v_s_206_);
                                v_pos_208_ = crate::leanh::lean_ctor_get(v_s_207_, 2);
                                crate::leanh::lean_inc(v_pos_208_);
                                v_errorMsg_209_ = crate::leanh::lean_ctor_get(v_s_207_, 4);
                                crate::leanh::lean_inc(v_errorMsg_209_);
                                v___x_222_ = crate::leanh::lean_box(0);
                                v___x_223_ = l_Option_instBEq_beq___at___00__private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse_spec__0(v_errorMsg_209_, v___x_222_);
                                if v___x_223_ == 0 {
                                    v___y_211_ = v___x_203_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___y_211_ = v___x_201_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_224_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__6;
                            v___x_225_ = crate::leanh::lean_alloc_closure(l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse as *mut core::ffi::c_void, 5, 3);
                            crate::leanh::lean_closure_set(v___x_225_, 0, v_p_185_);
                            crate::leanh::lean_closure_set(v___x_225_, 1, v_stackSize_186_);
                            crate::leanh::lean_closure_set(v___x_225_, 2, v_startPos_187_);
                            v___x_226_ =
                                l_Lean_Parser_andthenFn(v___x_224_, v___x_225_, v_c_188_, v_s_197_);
                            return v___x_226_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_185_);
                        v___x_227_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__1;
                        v_s_228_ = l_Lean_Parser_mkNodeToken(
                            v___x_227_,
                            v_startPos_187_,
                            v___x_194_,
                            v_c_188_,
                            v_s_197_,
                        );
                        v___x_229_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4;
                        v___x_230_ = l_Lean_Parser_ParserState_mkNode(
                            v_s_228_,
                            v___x_229_,
                            v_stackSize_186_,
                        );
                        crate::leanh::lean_dec(v_stackSize_186_);
                        return v___x_230_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_c_188_);
                    crate::leanh::lean_dec(v_startPos_187_);
                    crate::leanh::lean_dec_ref(v_p_185_);
                    v___x_231_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__7;
                    v_s_232_ = l_Lean_Parser_ParserState_mkError(v_s_189_, v___x_231_);
                    v___x_233_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4;
                    v___x_234_ =
                        l_Lean_Parser_ParserState_mkNode(v_s_232_, v___x_233_, v_stackSize_186_);
                    crate::leanh::lean_dec(v_stackSize_186_);
                    return v___x_234_;
                }
            }
            1 => {
                if v___y_211_ == 0 {
                    v_curr_212_ = lean_string_utf8_get(v_inputString_193_, v_pos_208_);
                    v___x_213_ = 125;
                    v___x_214_ = lean_uint32_dec_eq(v_curr_212_, v___x_213_);
                    if v___x_214_ == 0 {
                        crate::leanh::lean_dec(v_pos_208_);
                        crate::leanh::lean_dec_ref(v_c_188_);
                        crate::leanh::lean_dec_ref(v_p_185_);
                        v___x_215_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__2;
                        v_s_216_ = l_Lean_Parser_ParserState_mkError(v_s_207_, v___x_215_);
                        v___x_217_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4;
                        v___x_218_ = l_Lean_Parser_ParserState_mkNode(
                            v_s_216_,
                            v___x_217_,
                            v_stackSize_186_,
                        );
                        crate::leanh::lean_dec(v_stackSize_186_);
                        return v___x_218_;
                    } else {
                        v___x_219_ = lean_string_utf8_next(v_inputString_193_, v_pos_208_);
                        v_s_220_ = l_Lean_Parser_ParserState_setPos(v_s_207_, v___x_219_);
                        v_startPos_187_ = v_pos_208_;
                        v_s_189_ = v_s_220_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_pos_208_);
                    crate::leanh::lean_dec_ref(v_c_188_);
                    crate::leanh::lean_dec(v_stackSize_186_);
                    crate::leanh::lean_dec_ref(v_p_185_);
                    return v_s_207_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_interpolatedStrFn(
    mut v_p_236_: *mut crate::leanh::LeanObject,
    mut v_c_237_: *mut crate::leanh::LeanObject,
    mut v_s_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: u8 = 0;
    let mut v_inputString_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_246_: u32 = 0;
    let mut v___x_247_: u32 = 0;
    let mut v___x_248_: u8 = 0;
    let mut v_stackSize_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_242_ = crate::leanh::lean_ctor_get(v_s_238_, 2);
                v_toInputContext_243_ = crate::leanh::lean_ctor_get(v_c_237_, 0);
                v___x_244_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_243_, v_pos_242_);
                if v___x_244_ == 0 {
                    v_inputString_245_ = crate::leanh::lean_ctor_get(v_toInputContext_243_, 0);
                    v_curr_246_ = lean_string_utf8_get(v_inputString_245_, v_pos_242_);
                    v___x_247_ = 34;
                    v___x_248_ = lean_uint32_dec_eq(v_curr_246_, v___x_247_);
                    if v___x_248_ == 0 {
                        crate::leanh::lean_dec_ref(v_c_237_);
                        crate::leanh::lean_dec_ref(v_p_236_);
                        state = 1;
                        continue;
                    } else {
                        if v___x_244_ == 0 {
                            crate::leanh::lean_inc(v_pos_242_);
                            v_stackSize_249_ = l_Lean_Parser_ParserState_stackSize(v_s_238_);
                            v_s_250_ =
                                l_Lean_Parser_ParserState_next(v_s_238_, v_c_237_, v_pos_242_);
                            v___x_251_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse(v_p_236_, v_stackSize_249_, v_pos_242_, v_c_237_, v_s_250_);
                            return v___x_251_;
                        } else {
                            crate::leanh::lean_dec_ref(v_c_237_);
                            crate::leanh::lean_dec_ref(v_p_236_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_c_237_);
                    crate::leanh::lean_dec_ref(v_p_236_);
                    v___x_252_ = crate::leanh::lean_box(0);
                    v___x_253_ = l_Lean_Parser_ParserState_mkEOIError(v_s_238_, v___x_252_);
                    return v___x_253_;
                }
            }
            1 => {
                v___x_240_ = l_Lean_Parser_interpolatedStrFn___closed__0;
                v___x_241_ = l_Lean_Parser_ParserState_mkError(v_s_238_, v___x_240_);
                return v___x_241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_255_ = l_Lean_Parser_interpolatedStrNoAntiquot___closed__0;
    v___x_256_ = l_Lean_Parser_mkAtomicInfo(v___x_255_);
    return v___x_256_;
}
pub unsafe fn l_Lean_Parser_interpolatedStrNoAntiquot(
    mut v_p_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_262_: u8 = 0;
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_268_: u8 = 0;
    let mut v_unused_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_258_ = l_Lean_Parser_withoutPosition(v_p_257_);
                v_fn_259_ = crate::leanh::lean_ctor_get(v___x_258_, 1);
                v_isSharedCheck_268_ = (!crate::leanh::lean_is_exclusive(v___x_258_)) as u8;
                if v_isSharedCheck_268_ == 0 {
                    v_unused_269_ = crate::leanh::lean_ctor_get(v___x_258_, 0);
                    crate::leanh::lean_dec(v_unused_269_);
                    v___x_261_ = v___x_258_;
                    v_isShared_262_ = v_isSharedCheck_268_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fn_259_);
                    crate::leanh::lean_dec(v___x_258_);
                    v___x_261_ = crate::leanh::lean_box(0);
                    v_isShared_262_ = v_isSharedCheck_268_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_263_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Parser_interpolatedStrNoAntiquot___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Parser_interpolatedStrNoAntiquot___closed__1_once
                    ),
                    _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1,
                );
                v___x_264_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Parser_interpolatedStrFn as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_264_, 0, v_fn_259_);
                if v_isShared_262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_261_, 1, v___x_264_);
                    crate::leanh::lean_ctor_set(v___x_261_, 0, v___x_263_);
                    v___x_266_ = v___x_261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_267_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_264_);
                    v___x_266_ = v_reuseFailAlloc_267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Parser_interpolatedStr___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_270_: u8 = 0;
    let mut v___x_271_: u8 = 0;
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = 0;
    v___x_271_ = 1;
    v___x_272_ =
        l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStrFn_parse___closed__4;
    v___x_273_ = l_Lean_Parser_interpolatedStrNoAntiquot___closed__0;
    v___x_274_ = l_Lean_Parser_mkAntiquot(v___x_273_, v___x_272_, v___x_271_, v___x_270_);
    return v___x_274_;
}
pub unsafe fn l_Lean_Parser_interpolatedStr(
    mut v_p_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_280_: u8 = 0;
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_288_: u8 = 0;
    let mut v_unused_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_276_ = l_Lean_Parser_withoutPosition(v_p_275_);
                v_fn_277_ = crate::leanh::lean_ctor_get(v___x_276_, 1);
                v_isSharedCheck_288_ = (!crate::leanh::lean_is_exclusive(v___x_276_)) as u8;
                if v_isSharedCheck_288_ == 0 {
                    v_unused_289_ = crate::leanh::lean_ctor_get(v___x_276_, 0);
                    crate::leanh::lean_dec(v_unused_289_);
                    v___x_279_ = v___x_276_;
                    v_isShared_280_ = v_isSharedCheck_288_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fn_277_);
                    crate::leanh::lean_dec(v___x_276_);
                    v___x_279_ = crate::leanh::lean_box(0);
                    v_isShared_280_ = v_isSharedCheck_288_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_281_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Parser_interpolatedStr___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Parser_interpolatedStr___closed__0_once),
                    _init_l_Lean_Parser_interpolatedStr___closed__0,
                );
                v___x_282_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Parser_interpolatedStrNoAntiquot___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Parser_interpolatedStrNoAntiquot___closed__1_once
                    ),
                    _init_l_Lean_Parser_interpolatedStrNoAntiquot___closed__1,
                );
                v___x_283_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Parser_interpolatedStrFn as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_283_, 0, v_fn_277_);
                if v_isShared_280_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_279_, 1, v___x_283_);
                    crate::leanh::lean_ctor_set(v___x_279_, 0, v___x_282_);
                    v___x_285_ = v___x_279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_287_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_283_);
                    v___x_285_ = v_reuseFailAlloc_287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_286_ = l_Lean_Parser_withAntiquot(v___x_281_, v___x_285_);
                return v___x_286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__2;
    v___x_299_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___closed__3;
    v___x_300_ = l_Lean_addBuiltinDocString(v___x_298_, v___x_299_);
    return v___x_300_;
}
pub unsafe fn l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1___boxed(
    mut v_a_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_302_ = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1();
    return v_res_302_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_StrInterpolation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_StrInterpolation_0__Lean_Parser_interpolatedStr___regBuiltin_Lean_Parser_interpolatedStr_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_StrInterpolation(
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
pub unsafe fn initialize_Lean_Parser_StrInterpolation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_StrInterpolation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_StrInterpolation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Parser_StrInterpolation(builtin);
}
