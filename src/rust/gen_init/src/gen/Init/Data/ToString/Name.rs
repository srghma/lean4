// Lean compiler output
// Module: Init.Data.ToString.Name
// Imports: Init.Data.String.Substring Init.Data.String.TakeDrop Init.Data.String.Search
use crate::ffi::{
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_append, lean_string_get_byte_fast,
    lean_string_is_valid_pos, lean_string_memcmp, lean_string_push, lean_string_utf8_byte_size,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint8_dec_eq, lean_uint8_dec_le,
    lean_uint32_dec_eq, lean_uint32_dec_le, lean_uint32_to_uint8,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_get_x3f;
use crate::r#gen::Init::Data::String::Defs::l_String_instInhabitedSlice;
use crate::r#gen::Init::Data::String::Pattern::Basic::{
    l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2,
    l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed,
};
use crate::r#gen::Init::Data::String::Pattern::Pred::l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    l_String_Slice_Pos_skipWhile___redArg, l_String_Slice_contains___redArg,
};
use crate::r#gen::Init::Data::String::Substring::{
    initialize_Init_Data_String_Substring, l_Substring_Raw_nextn,
    runtime_initialize_Init_Data_String_Substring,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Name_getRoot, l_Lean_idBeginEscape, l_Lean_idEndEscape, l_Lean_isIdEndEscape___boxed,
    l_Lean_isIdRest___boxed, l_Lean_isLetterLike, l_Lean_isSubScriptAlnum,
    lean_is_inaccessible_user_name,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_hasMacroScopes, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0: u8 =
    0;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1: u8 =
    0;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2: u8 =
    0;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3: u8 =
    0;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4: u8 =
    0;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5: u8 =
    0;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6: u8 =
    0;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7: u8 =
    0;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8: u8 =
    0;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9: u8 =
    0;
pub static l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_isIdRest___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0_value:
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
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0_value)
        as *mut leanh::LeanObject;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Name_escapePart___lam__0___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_isIdEndEscape___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Name_escapePart___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_escapePart___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Name_escapePart___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Name_escapePart___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Name_escapePart___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_escapePart___lam__0 as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Name_escapePart___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_escapePart___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Name_escapePart___closed__1_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Name_escapePart___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Name_escapePart___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_escapePart___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Name_toStringWithSep___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0],
    };
static mut l_Lean_Name_toStringWithSep___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_toStringWithSep___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_toStringWithSep___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_toStringWithSep___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Name_toStringWithSep___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_toStringWithSep___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__0_value) as *mut leanh::LeanObject,13286986945483979944 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [35, 0]};
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Name_toStringWithToken___closed__0_value: leanh::LeanStringObject<2> =
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
        m_data: [46, 0],
    };
static mut l_Lean_Name_toStringWithToken___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_toStringWithToken___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Name_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Name_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0()
-> u8 {
    let mut v___x_754_: u32 = 0;
    let mut v___x_755_: u8 = 0;
    v___x_754_ = 95;
    v___x_755_ = lean_uint32_to_uint8(v___x_754_);
    return v___x_755_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1()
-> u8 {
    let mut v___x_756_: u32 = 0;
    let mut v___x_757_: u8 = 0;
    v___x_756_ = 39;
    v___x_757_ = lean_uint32_to_uint8(v___x_756_);
    return v___x_757_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2()
-> u8 {
    let mut v___x_758_: u32 = 0;
    let mut v___x_759_: u8 = 0;
    v___x_758_ = 33;
    v___x_759_ = lean_uint32_to_uint8(v___x_758_);
    return v___x_759_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3()
-> u8 {
    let mut v___x_760_: u32 = 0;
    let mut v___x_761_: u8 = 0;
    v___x_760_ = 63;
    v___x_761_ = lean_uint32_to_uint8(v___x_760_);
    return v___x_761_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4()
-> u8 {
    let mut v___x_762_: u32 = 0;
    let mut v___x_763_: u8 = 0;
    v___x_762_ = 48;
    v___x_763_ = lean_uint32_to_uint8(v___x_762_);
    return v___x_763_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5()
-> u8 {
    let mut v___x_764_: u32 = 0;
    let mut v___x_765_: u8 = 0;
    v___x_764_ = 57;
    v___x_765_ = lean_uint32_to_uint8(v___x_764_);
    return v___x_765_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6()
-> u8 {
    let mut v___x_766_: u32 = 0;
    let mut v___x_767_: u8 = 0;
    v___x_766_ = 65;
    v___x_767_ = lean_uint32_to_uint8(v___x_766_);
    return v___x_767_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7()
-> u8 {
    let mut v___x_768_: u32 = 0;
    let mut v___x_769_: u8 = 0;
    v___x_768_ = 90;
    v___x_769_ = lean_uint32_to_uint8(v___x_768_);
    return v___x_769_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8()
-> u8 {
    let mut v___x_770_: u32 = 0;
    let mut v___x_771_: u8 = 0;
    v___x_770_ = 97;
    v___x_771_ = lean_uint32_to_uint8(v___x_770_);
    return v___x_771_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9()
-> u8 {
    let mut v___x_772_: u32 = 0;
    let mut v___x_773_: u8 = 0;
    v___x_772_ = 122;
    v___x_773_ = lean_uint32_to_uint8(v___x_772_);
    return v___x_773_;
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(
    mut v_s_774_: *mut leanh::LeanObject,
    mut v_i_775_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_781_: u8 = 0;
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: u8 = 0;
    let mut v___x_784_: u8 = 0;
    let mut v_c_785_: u8 = 0;
    let mut v___y_787_: u8 = 0;
    let mut v___x_788_: u8 = 0;
    let mut v___x_789_: u8 = 0;
    let mut v___x_790_: u8 = 0;
    let mut v___x_791_: u8 = 0;
    let mut v___x_792_: u8 = 0;
    let mut v___x_793_: u8 = 0;
    let mut v___x_794_: u8 = 0;
    let mut v___x_795_: u8 = 0;
    let mut v___y_797_: u8 = 0;
    let mut v___x_798_: u8 = 0;
    let mut v___x_799_: u8 = 0;
    let mut v___x_800_: u8 = 0;
    let mut v___x_801_: u8 = 0;
    let mut v___y_803_: u8 = 0;
    let mut v___x_804_: u8 = 0;
    let mut v___x_805_: u8 = 0;
    let mut v___x_806_: u8 = 0;
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: u8 = 0;
    let mut v___x_809_: u8 = 0;
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_782_ = lean_string_utf8_byte_size(v_s_774_);
                v___x_783_ = lean_nat_dec_lt(v_i_775_, v___x_782_);
                if v___x_783_ == 0 {
                    leanh::lean_dec(v_i_775_);
                    v___x_784_ = 1;
                    return v___x_784_;
                } else {
                    leanh::lean_inc(v_i_775_);
                    v_c_785_ = lean_string_get_byte_fast(v_s_774_, v_i_775_);
                    v___x_808_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
                    v___x_809_ = lean_uint8_dec_le(v___x_808_, v_c_785_);
                    if v___x_809_ == 0 {
                        v___y_803_ = v___x_809_;
                        state = 5;
                        continue;
                    } else {
                        v___x_810_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
                        v___x_811_ = lean_uint8_dec_le(v_c_785_, v___x_810_);
                        v___y_803_ = v___x_811_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_777_ = leanh::lean_unsigned_to_nat(1);
                v___x_778_ = lean_nat_add(v_i_775_, v___x_777_);
                leanh::lean_dec(v_i_775_);
                v_i_775_ = v___x_778_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_781_ == 0 {
                    leanh::lean_dec(v_i_775_);
                    return v___y_781_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_787_ == 0 {
                    v___x_788_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
                    v___x_789_ = lean_uint8_dec_eq(v_c_785_, v___x_788_);
                    if v___x_789_ == 0 {
                        v___x_790_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__1);
                        v___x_791_ = lean_uint8_dec_eq(v_c_785_, v___x_790_);
                        if v___x_791_ == 0 {
                            v___x_792_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__2);
                            v___x_793_ = lean_uint8_dec_eq(v_c_785_, v___x_792_);
                            if v___x_793_ == 0 {
                                v___x_794_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__3);
                                v___x_795_ = lean_uint8_dec_eq(v_c_785_, v___x_794_);
                                v___y_781_ = v___x_795_;
                                state = 2;
                                continue;
                            } else {
                                v___y_781_ = v___x_793_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_781_ = v___x_791_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_781_ = v___x_789_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v___y_797_ == 0 {
                    v___x_798_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__4);
                    v___x_799_ = lean_uint8_dec_le(v___x_798_, v_c_785_);
                    if v___x_799_ == 0 {
                        v___y_787_ = v___x_799_;
                        state = 3;
                        continue;
                    } else {
                        v___x_800_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__5);
                        v___x_801_ = lean_uint8_dec_le(v_c_785_, v___x_800_);
                        v___y_787_ = v___x_801_;
                        state = 3;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v___y_803_ == 0 {
                    v___x_804_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
                    v___x_805_ = lean_uint8_dec_le(v___x_804_, v_c_785_);
                    if v___x_805_ == 0 {
                        v___y_797_ = v___x_805_;
                        state = 4;
                        continue;
                    } else {
                        v___x_806_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
                        v___x_807_ = lean_uint8_dec_le(v_c_785_, v___x_806_);
                        v___y_797_ = v___x_807_;
                        state = 4;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___boxed(
    mut v_s_812_: *mut leanh::LeanObject,
    mut v_i_813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_814_: u8 = 0;
    let mut v_r_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ =
        l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v_s_812_, v_i_813_);
    leanh::lean_dec_ref(v_s_812_);
    v_r_815_ = leanh::lean_box((v_res_814_) as usize);
    return v_r_815_;
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(
    mut v_s_816_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: u8 = 0;
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_821_: u8 = 0;
    let mut v___y_823_: u8 = 0;
    let mut v___x_824_: u8 = 0;
    let mut v___x_825_: u8 = 0;
    let mut v___y_827_: u8 = 0;
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: u8 = 0;
    let mut v___x_830_: u8 = 0;
    let mut v___x_831_: u8 = 0;
    let mut v___x_832_: u8 = 0;
    let mut v___x_833_: u8 = 0;
    let mut v___x_834_: u8 = 0;
    let mut v___x_835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_820_ = leanh::lean_unsigned_to_nat(0);
                v_c_821_ = lean_string_get_byte_fast(v_s_816_, v___x_820_);
                v___x_832_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
                v___x_833_ = lean_uint8_dec_le(v___x_832_, v_c_821_);
                if v___x_833_ == 0 {
                    v___y_827_ = v___x_833_;
                    state = 3;
                    continue;
                } else {
                    v___x_834_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
                    v___x_835_ = lean_uint8_dec_le(v_c_821_, v___x_834_);
                    v___y_827_ = v___x_835_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_818_ = leanh::lean_unsigned_to_nat(1);
                v___x_819_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(
                        v_s_816_, v___x_818_,
                    );
                return v___x_819_;
            }
            2 => {
                if v___y_823_ == 0 {
                    v___x_824_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
                    v___x_825_ = lean_uint8_dec_eq(v_c_821_, v___x_824_);
                    if v___x_825_ == 0 {
                        return v___x_825_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_827_ == 0 {
                    v___x_828_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
                    v___x_829_ = lean_uint8_dec_le(v___x_828_, v_c_821_);
                    if v___x_829_ == 0 {
                        v___y_823_ = v___x_829_;
                        state = 2;
                        continue;
                    } else {
                        v___x_830_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
                        v___x_831_ = lean_uint8_dec_le(v_c_821_, v___x_830_);
                        v___y_823_ = v___x_831_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(
    mut v_s_836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_837_: u8 = 0;
    let mut v_r_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_837_ =
        l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___redArg(v_s_836_);
    leanh::lean_dec_ref(v_s_836_);
    v_r_838_ = leanh::lean_box((v_res_837_) as usize);
    return v_r_838_;
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(
    mut v_s_839_: *mut leanh::LeanObject,
    mut v_h_840_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_845_: u8 = 0;
    let mut v___y_847_: u8 = 0;
    let mut v___x_848_: u8 = 0;
    let mut v___x_849_: u8 = 0;
    let mut v___y_851_: u8 = 0;
    let mut v___x_852_: u8 = 0;
    let mut v___x_853_: u8 = 0;
    let mut v___x_854_: u8 = 0;
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: u8 = 0;
    let mut v___x_857_: u8 = 0;
    let mut v___x_858_: u8 = 0;
    let mut v___x_859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_844_ = leanh::lean_unsigned_to_nat(0);
                v_c_845_ = lean_string_get_byte_fast(v_s_839_, v___x_844_);
                v___x_856_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
                v___x_857_ = lean_uint8_dec_le(v___x_856_, v_c_845_);
                if v___x_857_ == 0 {
                    v___y_851_ = v___x_857_;
                    state = 3;
                    continue;
                } else {
                    v___x_858_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
                    v___x_859_ = lean_uint8_dec_le(v_c_845_, v___x_858_);
                    v___y_851_ = v___x_859_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_842_ = leanh::lean_unsigned_to_nat(1);
                v___x_843_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(
                        v_s_839_, v___x_842_,
                    );
                return v___x_843_;
            }
            2 => {
                if v___y_847_ == 0 {
                    v___x_848_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
                    v___x_849_ = lean_uint8_dec_eq(v_c_845_, v___x_848_);
                    if v___x_849_ == 0 {
                        return v___x_849_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_851_ == 0 {
                    v___x_852_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
                    v___x_853_ = lean_uint8_dec_le(v___x_852_, v_c_845_);
                    if v___x_853_ == 0 {
                        v___y_847_ = v___x_853_;
                        state = 2;
                        continue;
                    } else {
                        v___x_854_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
                        v___x_855_ = lean_uint8_dec_le(v_c_845_, v___x_854_);
                        v___y_847_ = v___x_855_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii___boxed(
    mut v_s_860_: *mut leanh::LeanObject,
    mut v_h_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_862_: u8 = 0;
    let mut v_r_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_862_ =
        l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAscii(v_s_860_, v_h_861_);
    leanh::lean_dec_ref(v_s_860_);
    v_r_863_ = leanh::lean_box((v_res_862_) as usize);
    return v_r_863_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ =
        l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__2;
    v___x_868_ = leanh::lean_unsigned_to_nat(14);
    v___x_869_ = leanh::lean_unsigned_to_nat(22);
    v___x_870_ =
        l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__1;
    v___x_871_ =
        l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__0;
    v___x_872_ =
        l_mkPanicMessageWithDecl(v___x_871_, v___x_870_, v___x_869_, v___x_868_, v___x_867_);
    return v___x_872_;
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(
    mut v_s_874_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: u8 = 0;
    let mut v___y_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_906_: u8 = 0;
    let mut v___y_908_: u32 = 0;
    let mut v___y_909_: u8 = 0;
    let mut v___x_910_: u32 = 0;
    let mut v___x_911_: u8 = 0;
    let mut v___x_912_: u8 = 0;
    let mut v___y_914_: u32 = 0;
    let mut v___x_915_: u32 = 0;
    let mut v___x_916_: u8 = 0;
    let mut v___x_917_: u32 = 0;
    let mut v___x_918_: u8 = 0;
    let mut v___y_920_: u32 = 0;
    let mut v___x_921_: u32 = 0;
    let mut v___x_922_: u8 = 0;
    let mut v___x_923_: u32 = 0;
    let mut v___x_924_: u8 = 0;
    let mut v___y_926_: u8 = 0;
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: u32 = 0;
    let mut v_val_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: u32 = 0;
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_938_: u8 = 0;
    let mut v___y_940_: u8 = 0;
    let mut v___x_941_: u8 = 0;
    let mut v___x_942_: u8 = 0;
    let mut v___y_944_: u8 = 0;
    let mut v___x_945_: u8 = 0;
    let mut v___x_946_: u8 = 0;
    let mut v___x_947_: u8 = 0;
    let mut v___x_948_: u8 = 0;
    let mut v___x_949_: u8 = 0;
    let mut v___x_950_: u8 = 0;
    let mut v___x_951_: u8 = 0;
    let mut v___x_952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_937_ = leanh::lean_unsigned_to_nat(0);
                v_c_938_ = lean_string_get_byte_fast(v_s_874_, v___x_937_);
                v___x_949_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
                v___x_950_ = lean_uint8_dec_le(v___x_949_, v_c_938_);
                if v___x_950_ == 0 {
                    v___y_944_ = v___x_950_;
                    state = 11;
                    continue;
                } else {
                    v___x_951_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
                    v___x_952_ = lean_uint8_dec_le(v_c_938_, v___x_951_);
                    v___y_944_ = v___x_952_;
                    state = 11;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_877_);
                v___x_881_ =
                    l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_877_);
                v___x_882_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___y_878_, v___y_876_, v___x_881_);
                leanh::lean_dec_ref(v___y_878_);
                v___x_883_ = lean_nat_sub(v_endExclusive_880_, v_startInclusive_879_);
                leanh::lean_dec(v_startInclusive_879_);
                leanh::lean_dec(v_endExclusive_880_);
                v___x_884_ = lean_nat_dec_eq(v___x_882_, v___x_883_);
                leanh::lean_dec(v___x_883_);
                leanh::lean_dec(v___x_882_);
                return v___x_884_;
            }
            2 => {
                v___x_889_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
                v___x_890_ = l_panic___redArg(v___y_887_, v___x_889_);
                v_startInclusive_891_ = leanh::lean_ctor_get(v___x_890_, 1);
                leanh::lean_inc(v_startInclusive_891_);
                v_endExclusive_892_ = leanh::lean_ctor_get(v___x_890_, 2);
                leanh::lean_inc(v_endExclusive_892_);
                v___y_876_ = v___y_886_;
                v___y_877_ = v___y_888_;
                v___y_878_ = v___x_890_;
                v_startInclusive_879_ = v_startInclusive_891_;
                v_endExclusive_880_ = v_endExclusive_892_;
                state = 1;
                continue;
            }
            3 => {
                v___x_894_ = leanh::lean_unsigned_to_nat(0);
                v___x_895_ = lean_string_utf8_byte_size(v_s_874_);
                leanh::lean_inc_ref(v_s_874_);
                v___x_896_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_896_, 0, v_s_874_);
                leanh::lean_ctor_set(v___x_896_, 1, v___x_894_);
                leanh::lean_ctor_set(v___x_896_, 2, v___x_895_);
                v___x_897_ = leanh::lean_unsigned_to_nat(1);
                v___x_898_ = l_Substring_Raw_nextn(v___x_896_, v___x_897_, v___x_894_);
                leanh::lean_dec_ref_known(v___x_896_, 3);
                v___x_899_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4;
                v___x_900_ = l_String_instInhabitedSlice;
                v___x_901_ = lean_string_is_valid_pos(v_s_874_, v___x_898_);
                if v___x_901_ == 0 {
                    leanh::lean_dec(v___x_898_);
                    leanh::lean_dec_ref(v_s_874_);
                    v___y_886_ = v___x_894_;
                    v___y_887_ = v___x_900_;
                    v___y_888_ = v___x_899_;
                    state = 2;
                    continue;
                } else {
                    v___x_902_ = lean_string_is_valid_pos(v_s_874_, v___x_895_);
                    if v___x_902_ == 0 {
                        leanh::lean_dec(v___x_898_);
                        leanh::lean_dec_ref(v_s_874_);
                        v___y_886_ = v___x_894_;
                        v___y_887_ = v___x_900_;
                        v___y_888_ = v___x_899_;
                        state = 2;
                        continue;
                    } else {
                        v___x_903_ = lean_nat_dec_le(v___x_898_, v___x_895_);
                        if v___x_903_ == 0 {
                            leanh::lean_dec(v___x_898_);
                            leanh::lean_dec_ref(v_s_874_);
                            v___y_886_ = v___x_894_;
                            v___y_887_ = v___x_900_;
                            v___y_888_ = v___x_899_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_898_);
                            v___x_904_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_904_, 0, v_s_874_);
                            leanh::lean_ctor_set(v___x_904_, 1, v___x_898_);
                            leanh::lean_ctor_set(v___x_904_, 2, v___x_895_);
                            v___y_876_ = v___x_894_;
                            v___y_877_ = v___x_899_;
                            v___y_878_ = v___x_904_;
                            v_startInclusive_879_ = v___x_898_;
                            v_endExclusive_880_ = v___x_895_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v___y_906_ == 0 {
                    leanh::lean_dec_ref(v_s_874_);
                    return v___y_906_;
                } else {
                    state = 3;
                    continue;
                }
            }
            5 => {
                if v___y_909_ == 0 {
                    v___x_910_ = 95;
                    v___x_911_ = lean_uint32_dec_eq(v___y_908_, v___x_910_);
                    if v___x_911_ == 0 {
                        v___x_912_ = l_Lean_isLetterLike(v___y_908_);
                        v___y_906_ = v___x_912_;
                        state = 4;
                        continue;
                    } else {
                        v___y_906_ = v___x_911_;
                        state = 4;
                        continue;
                    }
                } else {
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_915_ = 97;
                v___x_916_ = lean_uint32_dec_le(v___x_915_, v___y_914_);
                if v___x_916_ == 0 {
                    v___y_908_ = v___y_914_;
                    v___y_909_ = v___x_916_;
                    state = 5;
                    continue;
                } else {
                    v___x_917_ = 122;
                    v___x_918_ = lean_uint32_dec_le(v___y_914_, v___x_917_);
                    v___y_908_ = v___y_914_;
                    v___y_909_ = v___x_918_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_921_ = 65;
                v___x_922_ = lean_uint32_dec_le(v___x_921_, v___y_920_);
                if v___x_922_ == 0 {
                    v___y_914_ = v___y_920_;
                    state = 6;
                    continue;
                } else {
                    v___x_923_ = 90;
                    v___x_924_ = lean_uint32_dec_le(v___y_920_, v___x_923_);
                    if v___x_924_ == 0 {
                        v___y_914_ = v___y_920_;
                        state = 6;
                        continue;
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            8 => {
                if v___y_926_ == 0 {
                    v___x_927_ = leanh::lean_unsigned_to_nat(0);
                    v___x_928_ = lean_string_utf8_byte_size(v_s_874_);
                    leanh::lean_inc_ref(v_s_874_);
                    v___x_929_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_929_, 0, v_s_874_);
                    leanh::lean_ctor_set(v___x_929_, 1, v___x_927_);
                    leanh::lean_ctor_set(v___x_929_, 2, v___x_928_);
                    v___x_930_ = l_String_Slice_Pos_get_x3f(v___x_929_, v___x_927_);
                    leanh::lean_dec_ref_known(v___x_929_, 3);
                    if leanh::lean_obj_tag(v___x_930_) == 0 {
                        v___x_931_ = 65;
                        v___y_920_ = v___x_931_;
                        state = 7;
                        continue;
                    } else {
                        v_val_932_ = leanh::lean_ctor_get(v___x_930_, 0);
                        leanh::lean_inc(v_val_932_);
                        leanh::lean_dec_ref_known(v___x_930_, 1);
                        v___x_933_ = leanh::lean_unbox_uint32(v_val_932_);
                        leanh::lean_dec(v_val_932_);
                        v___y_920_ = v___x_933_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_s_874_);
                    return v___y_926_;
                }
            }
            9 => {
                v___x_935_ = leanh::lean_unsigned_to_nat(1);
                v___x_936_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(
                        v_s_874_, v___x_935_,
                    );
                v___y_926_ = v___x_936_;
                state = 8;
                continue;
            }
            10 => {
                if v___y_940_ == 0 {
                    v___x_941_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
                    v___x_942_ = lean_uint8_dec_eq(v_c_938_, v___x_941_);
                    if v___x_942_ == 0 {
                        v___y_926_ = v___x_942_;
                        state = 8;
                        continue;
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            11 => {
                if v___y_944_ == 0 {
                    v___x_945_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
                    v___x_946_ = lean_uint8_dec_le(v___x_945_, v_c_938_);
                    if v___x_946_ == 0 {
                        v___y_940_ = v___x_946_;
                        state = 10;
                        continue;
                    } else {
                        v___x_947_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
                        v___x_948_ = lean_uint8_dec_le(v_c_938_, v___x_947_);
                        v___y_940_ = v___x_948_;
                        state = 10;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___boxed(
    mut v_s_953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_954_: u8 = 0;
    let mut v_r_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_954_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg(v_s_953_);
    v_r_955_ = leanh::lean_box((v_res_954_) as usize);
    return v_r_955_;
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(
    mut v_s_956_: *mut leanh::LeanObject,
    mut v_h_957_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: u8 = 0;
    let mut v___y_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    let mut v___x_985_: u8 = 0;
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_989_: u8 = 0;
    let mut v___y_991_: u32 = 0;
    let mut v___y_992_: u8 = 0;
    let mut v___x_993_: u32 = 0;
    let mut v___x_994_: u8 = 0;
    let mut v___x_995_: u8 = 0;
    let mut v___y_997_: u32 = 0;
    let mut v___x_998_: u32 = 0;
    let mut v___x_999_: u8 = 0;
    let mut v___x_1000_: u32 = 0;
    let mut v___x_1001_: u8 = 0;
    let mut v___y_1003_: u32 = 0;
    let mut v___x_1004_: u32 = 0;
    let mut v___x_1005_: u8 = 0;
    let mut v___x_1006_: u32 = 0;
    let mut v___x_1007_: u8 = 0;
    let mut v___y_1009_: u8 = 0;
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: u32 = 0;
    let mut v_val_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: u32 = 0;
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: u8 = 0;
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1021_: u8 = 0;
    let mut v___y_1023_: u8 = 0;
    let mut v___x_1024_: u8 = 0;
    let mut v___x_1025_: u8 = 0;
    let mut v___y_1027_: u8 = 0;
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1029_: u8 = 0;
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: u8 = 0;
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1034_: u8 = 0;
    let mut v___x_1035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1020_ = leanh::lean_unsigned_to_nat(0);
                v_c_1021_ = lean_string_get_byte_fast(v_s_956_, v___x_1020_);
                v___x_1032_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
                v___x_1033_ = lean_uint8_dec_le(v___x_1032_, v_c_1021_);
                if v___x_1033_ == 0 {
                    v___y_1027_ = v___x_1033_;
                    state = 11;
                    continue;
                } else {
                    v___x_1034_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
                    v___x_1035_ = lean_uint8_dec_le(v_c_1021_, v___x_1034_);
                    v___y_1027_ = v___x_1035_;
                    state = 11;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_960_);
                v___x_964_ =
                    l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_960_);
                v___x_965_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___y_961_, v___y_959_, v___x_964_);
                leanh::lean_dec_ref(v___y_961_);
                v___x_966_ = lean_nat_sub(v_endExclusive_963_, v_startInclusive_962_);
                leanh::lean_dec(v_startInclusive_962_);
                leanh::lean_dec(v_endExclusive_963_);
                v___x_967_ = lean_nat_dec_eq(v___x_965_, v___x_966_);
                leanh::lean_dec(v___x_966_);
                leanh::lean_dec(v___x_965_);
                return v___x_967_;
            }
            2 => {
                v___x_972_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
                v___x_973_ = l_panic___redArg(v___y_970_, v___x_972_);
                v_startInclusive_974_ = leanh::lean_ctor_get(v___x_973_, 1);
                leanh::lean_inc(v_startInclusive_974_);
                v_endExclusive_975_ = leanh::lean_ctor_get(v___x_973_, 2);
                leanh::lean_inc(v_endExclusive_975_);
                v___y_959_ = v___y_969_;
                v___y_960_ = v___y_971_;
                v___y_961_ = v___x_973_;
                v_startInclusive_962_ = v_startInclusive_974_;
                v_endExclusive_963_ = v_endExclusive_975_;
                state = 1;
                continue;
            }
            3 => {
                v___x_977_ = leanh::lean_unsigned_to_nat(0);
                v___x_978_ = lean_string_utf8_byte_size(v_s_956_);
                leanh::lean_inc_ref(v_s_956_);
                v___x_979_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_979_, 0, v_s_956_);
                leanh::lean_ctor_set(v___x_979_, 1, v___x_977_);
                leanh::lean_ctor_set(v___x_979_, 2, v___x_978_);
                v___x_980_ = leanh::lean_unsigned_to_nat(1);
                v___x_981_ = l_Substring_Raw_nextn(v___x_979_, v___x_980_, v___x_977_);
                leanh::lean_dec_ref_known(v___x_979_, 3);
                v___x_982_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4;
                v___x_983_ = l_String_instInhabitedSlice;
                v___x_984_ = lean_string_is_valid_pos(v_s_956_, v___x_981_);
                if v___x_984_ == 0 {
                    leanh::lean_dec(v___x_981_);
                    leanh::lean_dec_ref(v_s_956_);
                    v___y_969_ = v___x_977_;
                    v___y_970_ = v___x_983_;
                    v___y_971_ = v___x_982_;
                    state = 2;
                    continue;
                } else {
                    v___x_985_ = lean_string_is_valid_pos(v_s_956_, v___x_978_);
                    if v___x_985_ == 0 {
                        leanh::lean_dec(v___x_981_);
                        leanh::lean_dec_ref(v_s_956_);
                        v___y_969_ = v___x_977_;
                        v___y_970_ = v___x_983_;
                        v___y_971_ = v___x_982_;
                        state = 2;
                        continue;
                    } else {
                        v___x_986_ = lean_nat_dec_le(v___x_981_, v___x_978_);
                        if v___x_986_ == 0 {
                            leanh::lean_dec(v___x_981_);
                            leanh::lean_dec_ref(v_s_956_);
                            v___y_969_ = v___x_977_;
                            v___y_970_ = v___x_983_;
                            v___y_971_ = v___x_982_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_981_);
                            v___x_987_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_987_, 0, v_s_956_);
                            leanh::lean_ctor_set(v___x_987_, 1, v___x_981_);
                            leanh::lean_ctor_set(v___x_987_, 2, v___x_978_);
                            v___y_959_ = v___x_977_;
                            v___y_960_ = v___x_982_;
                            v___y_961_ = v___x_987_;
                            v_startInclusive_962_ = v___x_981_;
                            v_endExclusive_963_ = v___x_978_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v___y_989_ == 0 {
                    leanh::lean_dec_ref(v_s_956_);
                    return v___y_989_;
                } else {
                    state = 3;
                    continue;
                }
            }
            5 => {
                if v___y_992_ == 0 {
                    v___x_993_ = 95;
                    v___x_994_ = lean_uint32_dec_eq(v___y_991_, v___x_993_);
                    if v___x_994_ == 0 {
                        v___x_995_ = l_Lean_isLetterLike(v___y_991_);
                        v___y_989_ = v___x_995_;
                        state = 4;
                        continue;
                    } else {
                        v___y_989_ = v___x_994_;
                        state = 4;
                        continue;
                    }
                } else {
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_998_ = 97;
                v___x_999_ = lean_uint32_dec_le(v___x_998_, v___y_997_);
                if v___x_999_ == 0 {
                    v___y_991_ = v___y_997_;
                    v___y_992_ = v___x_999_;
                    state = 5;
                    continue;
                } else {
                    v___x_1000_ = 122;
                    v___x_1001_ = lean_uint32_dec_le(v___y_997_, v___x_1000_);
                    v___y_991_ = v___y_997_;
                    v___y_992_ = v___x_1001_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_1004_ = 65;
                v___x_1005_ = lean_uint32_dec_le(v___x_1004_, v___y_1003_);
                if v___x_1005_ == 0 {
                    v___y_997_ = v___y_1003_;
                    state = 6;
                    continue;
                } else {
                    v___x_1006_ = 90;
                    v___x_1007_ = lean_uint32_dec_le(v___y_1003_, v___x_1006_);
                    if v___x_1007_ == 0 {
                        v___y_997_ = v___y_1003_;
                        state = 6;
                        continue;
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            8 => {
                if v___y_1009_ == 0 {
                    v___x_1010_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1011_ = lean_string_utf8_byte_size(v_s_956_);
                    leanh::lean_inc_ref(v_s_956_);
                    v___x_1012_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1012_, 0, v_s_956_);
                    leanh::lean_ctor_set(v___x_1012_, 1, v___x_1010_);
                    leanh::lean_ctor_set(v___x_1012_, 2, v___x_1011_);
                    v___x_1013_ = l_String_Slice_Pos_get_x3f(v___x_1012_, v___x_1010_);
                    leanh::lean_dec_ref_known(v___x_1012_, 3);
                    if leanh::lean_obj_tag(v___x_1013_) == 0 {
                        v___x_1014_ = 65;
                        v___y_1003_ = v___x_1014_;
                        state = 7;
                        continue;
                    } else {
                        v_val_1015_ = leanh::lean_ctor_get(v___x_1013_, 0);
                        leanh::lean_inc(v_val_1015_);
                        leanh::lean_dec_ref_known(v___x_1013_, 1);
                        v___x_1016_ = leanh::lean_unbox_uint32(v_val_1015_);
                        leanh::lean_dec(v_val_1015_);
                        v___y_1003_ = v___x_1016_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_s_956_);
                    return v___y_1009_;
                }
            }
            9 => {
                v___x_1018_ = leanh::lean_unsigned_to_nat(1);
                v___x_1019_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(
                        v_s_956_,
                        v___x_1018_,
                    );
                v___y_1009_ = v___x_1019_;
                state = 8;
                continue;
            }
            10 => {
                if v___y_1023_ == 0 {
                    v___x_1024_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
                    v___x_1025_ = lean_uint8_dec_eq(v_c_1021_, v___x_1024_);
                    if v___x_1025_ == 0 {
                        v___y_1009_ = v___x_1025_;
                        state = 8;
                        continue;
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            11 => {
                if v___y_1027_ == 0 {
                    v___x_1028_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
                    v___x_1029_ = lean_uint8_dec_le(v___x_1028_, v_c_1021_);
                    if v___x_1029_ == 0 {
                        v___y_1023_ = v___x_1029_;
                        state = 10;
                        continue;
                    } else {
                        v___x_1030_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
                        v___x_1031_ = lean_uint8_dec_le(v_c_1021_, v___x_1030_);
                        v___y_1023_ = v___x_1031_;
                        state = 10;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___boxed(
    mut v_s_1036_: *mut leanh::LeanObject,
    mut v_h_1037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1038_: u8 = 0;
    let mut v_r_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1038_ =
        l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape(v_s_1036_, v_h_1037_);
    v_r_1039_ = leanh::lean_box((v_res_1038_) as usize);
    return v_r_1039_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1041_: u32 = 0;
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1041_ = l_Lean_idBeginEscape;
    v___x_1042_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0;
    v___x_1043_ = lean_string_push(v___x_1042_, v___x_1041_);
    return v___x_1043_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1044_: u32 = 0;
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ = l_Lean_idEndEscape;
    v___x_1045_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__0;
    v___x_1046_ = lean_string_push(v___x_1045_, v___x_1044_);
    return v___x_1046_;
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_escape(
    mut v_s_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once
        ),
        _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1,
    );
    v___x_1049_ = lean_string_append(v___x_1048_, v_s_1047_);
    v___x_1050_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once
        ),
        _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2,
    );
    v___x_1051_ = lean_string_append(v___x_1049_, v___x_1050_);
    return v___x_1051_;
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_escape___boxed(
    mut v_s_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1053_ = l___private_Init_Data_ToString_Name_0__Lean_Name_escape(v_s_1052_);
    leanh::lean_dec_ref(v_s_1052_);
    return v_res_1053_;
}
pub unsafe fn _init_l_Lean_Name_escapePart___lam__0___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1055_ = l_Lean_Name_escapePart___lam__0___closed__0;
    v___x_1056_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1055_);
    return v___x_1056_;
}
pub unsafe fn l_Lean_Name_escapePart___lam__0(
    mut v_s_1057_: *mut leanh::LeanObject,
    mut v___y_1058_: *mut leanh::LeanObject,
    mut v___y_1059_: *mut leanh::LeanObject,
    mut v___y_1060_: *mut leanh::LeanObject,
    mut v___y_1061_: *mut leanh::LeanObject,
    mut v___y_1062_: *mut leanh::LeanObject,
    mut v___y_1063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Name_escapePart___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Name_escapePart___lam__0___closed__1_once),
        _init_l_Lean_Name_escapePart___lam__0___closed__1,
    );
    v___x_1065_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_1057_, v___x_1064_, v___y_1058_, leanh::lean_box(0), leanh::lean_box(0), v___y_1061_, v___y_1062_, v___y_1063_);
    return v___x_1065_;
}
pub unsafe fn l_Lean_Name_escapePart(
    mut v_s_1069_: *mut leanh::LeanObject,
    mut v_force_1070_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: u8 = 0;
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: u8 = 0;
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: u8 = 0;
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: u8 = 0;
    let mut v___x_1117_: u8 = 0;
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1120_: u8 = 0;
    let mut v___y_1122_: u32 = 0;
    let mut v___y_1123_: u8 = 0;
    let mut v___x_1124_: u32 = 0;
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: u8 = 0;
    let mut v___y_1128_: u32 = 0;
    let mut v___x_1129_: u32 = 0;
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1131_: u32 = 0;
    let mut v___x_1132_: u8 = 0;
    let mut v___y_1134_: u32 = 0;
    let mut v___x_1135_: u32 = 0;
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: u32 = 0;
    let mut v___x_1138_: u8 = 0;
    let mut v___y_1140_: u8 = 0;
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: u32 = 0;
    let mut v_val_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u32 = 0;
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: u8 = 0;
    let mut v_c_1150_: u8 = 0;
    let mut v___y_1152_: u8 = 0;
    let mut v___x_1153_: u8 = 0;
    let mut v___x_1154_: u8 = 0;
    let mut v___y_1156_: u8 = 0;
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: u8 = 0;
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: u8 = 0;
    let mut v___x_1162_: u8 = 0;
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1071_ = leanh::lean_unsigned_to_nat(0);
                v___x_1072_ = lean_string_utf8_byte_size(v_s_1069_);
                v___x_1073_ = lean_nat_dec_lt(v___x_1071_, v___x_1072_);
                if v___x_1073_ == 0 {
                    v___x_1074_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
                    v___x_1075_ = lean_string_append(v___x_1074_, v_s_1069_);
                    leanh::lean_dec_ref(v_s_1069_);
                    v___x_1076_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
                    v___x_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
                    v___x_1078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1078_, 0, v___x_1077_);
                    return v___x_1078_;
                } else {
                    v___f_1079_ = l_Lean_Name_escapePart___closed__0;
                    if v_force_1070_ == 0 {
                        v_c_1150_ = lean_string_get_byte_fast(v_s_1069_, v___x_1071_);
                        v___x_1161_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
                        v___x_1162_ = lean_uint8_dec_le(v___x_1161_, v_c_1150_);
                        if v___x_1162_ == 0 {
                            v___y_1156_ = v___x_1162_;
                            state = 12;
                            continue;
                        } else {
                            v___x_1163_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
                            v___x_1164_ = lean_uint8_dec_le(v_c_1150_, v___x_1163_);
                            v___y_1156_ = v___x_1164_;
                            state = 12;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1081_ = l_Lean_Name_escapePart___closed__1;
                leanh::lean_inc_ref(v_s_1069_);
                v___x_1082_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1082_, 0, v_s_1069_);
                leanh::lean_ctor_set(v___x_1082_, 1, v___x_1071_);
                leanh::lean_ctor_set(v___x_1082_, 2, v___x_1072_);
                v___x_1083_ =
                    l_String_Slice_contains___redArg(v___f_1079_, v___x_1082_, v___x_1081_);
                if v___x_1083_ == 0 {
                    v___x_1084_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
                    v___x_1085_ = lean_string_append(v___x_1084_, v_s_1069_);
                    leanh::lean_dec_ref(v_s_1069_);
                    v___x_1086_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
                    v___x_1087_ = lean_string_append(v___x_1085_, v___x_1086_);
                    v___x_1088_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1088_, 0, v___x_1087_);
                    return v___x_1088_;
                } else {
                    leanh::lean_dec_ref(v_s_1069_);
                    v___x_1089_ = leanh::lean_box(0);
                    return v___x_1089_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___y_1092_);
                v___x_1096_ =
                    l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___y_1092_);
                v___x_1097_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___y_1093_, v___y_1091_, v___x_1096_);
                leanh::lean_dec_ref(v___y_1093_);
                v___x_1098_ = lean_nat_sub(v_endExclusive_1095_, v_startInclusive_1094_);
                leanh::lean_dec(v_startInclusive_1094_);
                leanh::lean_dec(v_endExclusive_1095_);
                v___x_1099_ = lean_nat_dec_eq(v___x_1097_, v___x_1098_);
                leanh::lean_dec(v___x_1098_);
                leanh::lean_dec(v___x_1097_);
                if v___x_1099_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1100_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1100_, 0, v_s_1069_);
                    return v___x_1100_;
                }
            }
            3 => {
                v___x_1105_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
                v___x_1106_ = l_panic___redArg(v___y_1104_, v___x_1105_);
                v_startInclusive_1107_ = leanh::lean_ctor_get(v___x_1106_, 1);
                leanh::lean_inc(v_startInclusive_1107_);
                v_endExclusive_1108_ = leanh::lean_ctor_get(v___x_1106_, 2);
                leanh::lean_inc(v_endExclusive_1108_);
                v___y_1091_ = v___y_1102_;
                v___y_1092_ = v___y_1103_;
                v___y_1093_ = v___x_1106_;
                v_startInclusive_1094_ = v_startInclusive_1107_;
                v_endExclusive_1095_ = v_endExclusive_1108_;
                state = 2;
                continue;
            }
            4 => {
                leanh::lean_inc_ref(v_s_1069_);
                v___x_1110_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1110_, 0, v_s_1069_);
                leanh::lean_ctor_set(v___x_1110_, 1, v___x_1071_);
                leanh::lean_ctor_set(v___x_1110_, 2, v___x_1072_);
                v___x_1111_ = leanh::lean_unsigned_to_nat(1);
                v___x_1112_ = l_Substring_Raw_nextn(v___x_1110_, v___x_1111_, v___x_1071_);
                leanh::lean_dec_ref_known(v___x_1110_, 3);
                v___x_1113_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__4;
                v___x_1114_ = l_String_instInhabitedSlice;
                v___x_1115_ = lean_string_is_valid_pos(v_s_1069_, v___x_1112_);
                if v___x_1115_ == 0 {
                    leanh::lean_dec(v___x_1112_);
                    v___y_1102_ = v___x_1071_;
                    v___y_1103_ = v___x_1113_;
                    v___y_1104_ = v___x_1114_;
                    state = 3;
                    continue;
                } else {
                    v___x_1116_ = lean_string_is_valid_pos(v_s_1069_, v___x_1072_);
                    if v___x_1116_ == 0 {
                        leanh::lean_dec(v___x_1112_);
                        v___y_1102_ = v___x_1071_;
                        v___y_1103_ = v___x_1113_;
                        v___y_1104_ = v___x_1114_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1117_ = lean_nat_dec_le(v___x_1112_, v___x_1072_);
                        if v___x_1117_ == 0 {
                            leanh::lean_dec(v___x_1112_);
                            v___y_1102_ = v___x_1071_;
                            v___y_1103_ = v___x_1113_;
                            v___y_1104_ = v___x_1114_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_1112_);
                            leanh::lean_inc_ref(v_s_1069_);
                            v___x_1118_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_1118_, 0, v_s_1069_);
                            leanh::lean_ctor_set(v___x_1118_, 1, v___x_1112_);
                            leanh::lean_ctor_set(v___x_1118_, 2, v___x_1072_);
                            v___y_1091_ = v___x_1071_;
                            v___y_1092_ = v___x_1113_;
                            v___y_1093_ = v___x_1118_;
                            v_startInclusive_1094_ = v___x_1112_;
                            v_endExclusive_1095_ = v___x_1072_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v___y_1120_ == 0 {
                    state = 1;
                    continue;
                } else {
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v___y_1123_ == 0 {
                    v___x_1124_ = 95;
                    v___x_1125_ = lean_uint32_dec_eq(v___y_1122_, v___x_1124_);
                    if v___x_1125_ == 0 {
                        v___x_1126_ = l_Lean_isLetterLike(v___y_1122_);
                        v___y_1120_ = v___x_1126_;
                        state = 5;
                        continue;
                    } else {
                        v___y_1120_ = v___x_1125_;
                        state = 5;
                        continue;
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            7 => {
                v___x_1129_ = 97;
                v___x_1130_ = lean_uint32_dec_le(v___x_1129_, v___y_1128_);
                if v___x_1130_ == 0 {
                    v___y_1122_ = v___y_1128_;
                    v___y_1123_ = v___x_1130_;
                    state = 6;
                    continue;
                } else {
                    v___x_1131_ = 122;
                    v___x_1132_ = lean_uint32_dec_le(v___y_1128_, v___x_1131_);
                    v___y_1122_ = v___y_1128_;
                    v___y_1123_ = v___x_1132_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_1135_ = 65;
                v___x_1136_ = lean_uint32_dec_le(v___x_1135_, v___y_1134_);
                if v___x_1136_ == 0 {
                    v___y_1128_ = v___y_1134_;
                    state = 7;
                    continue;
                } else {
                    v___x_1137_ = 90;
                    v___x_1138_ = lean_uint32_dec_le(v___y_1134_, v___x_1137_);
                    if v___x_1138_ == 0 {
                        v___y_1128_ = v___y_1134_;
                        state = 7;
                        continue;
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            9 => {
                if v___y_1140_ == 0 {
                    leanh::lean_inc_ref(v_s_1069_);
                    v___x_1141_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1141_, 0, v_s_1069_);
                    leanh::lean_ctor_set(v___x_1141_, 1, v___x_1071_);
                    leanh::lean_ctor_set(v___x_1141_, 2, v___x_1072_);
                    v___x_1142_ = l_String_Slice_Pos_get_x3f(v___x_1141_, v___x_1071_);
                    leanh::lean_dec_ref_known(v___x_1141_, 3);
                    if leanh::lean_obj_tag(v___x_1142_) == 0 {
                        v___x_1143_ = 65;
                        v___y_1134_ = v___x_1143_;
                        state = 8;
                        continue;
                    } else {
                        v_val_1144_ = leanh::lean_ctor_get(v___x_1142_, 0);
                        leanh::lean_inc(v_val_1144_);
                        leanh::lean_dec_ref_known(v___x_1142_, 1);
                        v___x_1145_ = leanh::lean_unbox_uint32(v_val_1144_);
                        leanh::lean_dec(v_val_1144_);
                        v___y_1134_ = v___x_1145_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___x_1146_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1146_, 0, v_s_1069_);
                    return v___x_1146_;
                }
            }
            10 => {
                v___x_1148_ = leanh::lean_unsigned_to_nat(1);
                v___x_1149_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(
                        v_s_1069_,
                        v___x_1148_,
                    );
                v___y_1140_ = v___x_1149_;
                state = 9;
                continue;
            }
            11 => {
                if v___y_1152_ == 0 {
                    v___x_1153_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
                    v___x_1154_ = lean_uint8_dec_eq(v_c_1150_, v___x_1153_);
                    if v___x_1154_ == 0 {
                        v___y_1140_ = v___x_1154_;
                        state = 9;
                        continue;
                    } else {
                        state = 10;
                        continue;
                    }
                } else {
                    state = 10;
                    continue;
                }
            }
            12 => {
                if v___y_1156_ == 0 {
                    v___x_1157_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
                    v___x_1158_ = lean_uint8_dec_le(v___x_1157_, v_c_1150_);
                    if v___x_1158_ == 0 {
                        v___y_1152_ = v___x_1158_;
                        state = 11;
                        continue;
                    } else {
                        v___x_1159_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
                        v___x_1160_ = lean_uint8_dec_le(v_c_1150_, v___x_1159_);
                        v___y_1152_ = v___x_1160_;
                        state = 11;
                        continue;
                    }
                } else {
                    state = 10;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_escapePart___boxed(
    mut v_s_1165_: *mut leanh::LeanObject,
    mut v_force_1166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_force_boxed_1167_: u8 = 0;
    let mut v_res_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_force_boxed_1167_ = (leanh::lean_unbox(v_force_1166_) as u8);
    v_res_1168_ = l_Lean_Name_escapePart(v_s_1165_, v_force_boxed_1167_);
    return v_res_1168_;
}
pub unsafe fn l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(
    mut v_msg_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_String_instInhabitedSlice;
    v___x_1171_ = lean_panic_fn_borrowed(v___x_1170_, v_msg_1169_);
    return v___x_1171_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(
    mut v_s_1172_: *mut leanh::LeanObject,
    mut v_pos_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: u8 = 0;
    let mut v___y_1185_: u8 = 0;
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1189_: u32 = 0;
    let mut v___y_1191_: u8 = 0;
    let mut v___x_1192_: u32 = 0;
    let mut v___x_1193_: u8 = 0;
    let mut v___x_1194_: u32 = 0;
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: u32 = 0;
    let mut v___x_1197_: u8 = 0;
    let mut v___x_1198_: u32 = 0;
    let mut v___x_1199_: u8 = 0;
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1201_: u8 = 0;
    let mut v___y_1203_: u8 = 0;
    let mut v___x_1204_: u32 = 0;
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: u32 = 0;
    let mut v___x_1207_: u8 = 0;
    let mut v___x_1209_: u32 = 0;
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1211_: u32 = 0;
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1213_: u32 = 0;
    let mut v___x_1214_: u8 = 0;
    let mut v___x_1215_: u32 = 0;
    let mut v___x_1216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1174_ = leanh::lean_ctor_get(v_s_1172_, 0);
                v_startInclusive_1175_ = leanh::lean_ctor_get(v_s_1172_, 1);
                v_endExclusive_1176_ = leanh::lean_ctor_get(v_s_1172_, 2);
                v___x_1177_ = lean_nat_add(v_startInclusive_1175_, v_pos_1173_);
                v___x_1186_ = leanh::lean_unsigned_to_nat(0);
                v___x_1187_ = lean_nat_sub(v_endExclusive_1176_, v___x_1177_);
                v___x_1188_ = lean_nat_dec_eq(v___x_1186_, v___x_1187_);
                leanh::lean_dec(v___x_1187_);
                if v___x_1188_ == 0 {
                    v___x_1189_ = lean_string_utf8_get_fast(v_str_1174_, v___x_1177_);
                    v___x_1213_ = 65;
                    v___x_1214_ = lean_uint32_dec_le(v___x_1213_, v___x_1189_);
                    if v___x_1214_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        v___x_1215_ = 90;
                        v___x_1216_ = lean_uint32_dec_le(v___x_1189_, v___x_1215_);
                        if v___x_1216_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1177_);
                    return v_pos_1173_;
                }
            }
            1 => {
                v___x_1179_ = lean_string_utf8_next_fast(v_str_1174_, v___x_1177_);
                v___x_1180_ = lean_nat_sub(v___x_1179_, v___x_1177_);
                leanh::lean_dec(v___x_1177_);
                v___x_1181_ = lean_nat_add(v_pos_1173_, v___x_1180_);
                leanh::lean_dec(v___x_1180_);
                v___x_1182_ = lean_nat_dec_lt(v_pos_1173_, v___x_1181_);
                if v___x_1182_ == 0 {
                    leanh::lean_dec(v___x_1181_);
                    return v_pos_1173_;
                } else {
                    leanh::lean_dec(v_pos_1173_);
                    v_pos_1173_ = v___x_1181_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_1185_ == 0 {
                    leanh::lean_dec(v___x_1177_);
                    return v_pos_1173_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1191_ == 0 {
                    v___x_1192_ = 95;
                    v___x_1193_ = lean_uint32_dec_eq(v___x_1189_, v___x_1192_);
                    if v___x_1193_ == 0 {
                        v___x_1194_ = 39;
                        v___x_1195_ = lean_uint32_dec_eq(v___x_1189_, v___x_1194_);
                        if v___x_1195_ == 0 {
                            v___x_1196_ = 33;
                            v___x_1197_ = lean_uint32_dec_eq(v___x_1189_, v___x_1196_);
                            if v___x_1197_ == 0 {
                                v___x_1198_ = 63;
                                v___x_1199_ = lean_uint32_dec_eq(v___x_1189_, v___x_1198_);
                                if v___x_1199_ == 0 {
                                    v___x_1200_ = l_Lean_isLetterLike(v___x_1189_);
                                    if v___x_1200_ == 0 {
                                        v___x_1201_ = l_Lean_isSubScriptAlnum(v___x_1189_);
                                        v___y_1185_ = v___x_1201_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___y_1185_ = v___x_1200_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_1185_ = v___x_1199_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___y_1185_ = v___x_1197_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_1185_ = v___x_1195_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_1185_ = v___x_1193_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v___y_1203_ == 0 {
                    v___x_1204_ = 48;
                    v___x_1205_ = lean_uint32_dec_le(v___x_1204_, v___x_1189_);
                    if v___x_1205_ == 0 {
                        v___y_1191_ = v___x_1205_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1206_ = 57;
                        v___x_1207_ = lean_uint32_dec_le(v___x_1189_, v___x_1206_);
                        v___y_1191_ = v___x_1207_;
                        state = 3;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_1209_ = 97;
                v___x_1210_ = lean_uint32_dec_le(v___x_1209_, v___x_1189_);
                if v___x_1210_ == 0 {
                    v___y_1203_ = v___x_1210_;
                    state = 4;
                    continue;
                } else {
                    v___x_1211_ = 122;
                    v___x_1212_ = lean_uint32_dec_le(v___x_1189_, v___x_1211_);
                    v___y_1203_ = v___x_1212_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1___boxed(
    mut v_s_1217_: *mut leanh::LeanObject,
    mut v_pos_1218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1219_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v_s_1217_, v_pos_1218_);
    leanh::lean_dec_ref(v_s_1217_);
    return v_res_1219_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(
    mut v_s_1220_: *mut leanh::LeanObject,
    mut v_a_1221_: *mut leanh::LeanObject,
    mut v_b_1222_: u8,
) -> u8 {
    let mut v_str_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: u32 = 0;
    let mut v___x_1230_: u32 = 0;
    let mut v___x_1231_: u8 = 0;
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1223_ = leanh::lean_ctor_get(v_s_1220_, 0);
                v_startInclusive_1224_ = leanh::lean_ctor_get(v_s_1220_, 1);
                v_endExclusive_1225_ = leanh::lean_ctor_get(v_s_1220_, 2);
                v___x_1226_ = lean_nat_sub(v_endExclusive_1225_, v_startInclusive_1224_);
                v___x_1227_ = lean_nat_dec_eq(v_a_1221_, v___x_1226_);
                leanh::lean_dec(v___x_1226_);
                if v___x_1227_ == 0 {
                    v___x_1228_ = lean_nat_add(v_startInclusive_1224_, v_a_1221_);
                    leanh::lean_dec(v_a_1221_);
                    v___x_1229_ = lean_string_utf8_get_fast(v_str_1223_, v___x_1228_);
                    v___x_1230_ = 187;
                    v___x_1231_ = lean_uint32_dec_eq(v___x_1229_, v___x_1230_);
                    if v___x_1231_ == 0 {
                        v___x_1232_ = lean_string_utf8_next_fast(v_str_1223_, v___x_1228_);
                        leanh::lean_dec(v___x_1228_);
                        v___x_1233_ = lean_nat_sub(v___x_1232_, v_startInclusive_1224_);
                        v_a_1221_ = v___x_1233_;
                        v_b_1222_ = v___x_1231_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1228_);
                        return v___x_1231_;
                    }
                } else {
                    leanh::lean_dec(v_a_1221_);
                    return v_b_1222_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg___boxed(
    mut v_s_1235_: *mut leanh::LeanObject,
    mut v_a_1236_: *mut leanh::LeanObject,
    mut v_b_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1238_: u8 = 0;
    let mut v_res_1239_: u8 = 0;
    let mut v_r_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1238_ = (leanh::lean_unbox(v_b_1237_) as u8);
    v_res_1239_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_1235_, v_a_1236_, v_b_boxed_1238_);
    leanh::lean_dec_ref(v_s_1235_);
    v_r_1240_ = leanh::lean_box((v_res_1239_) as usize);
    return v_r_1240_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(
    mut v_s_1241_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_searcher_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: u8 = 0;
    let mut v___x_1244_: u8 = 0;
    v_searcher_1242_ = leanh::lean_unsigned_to_nat(0);
    v___x_1243_ = 0;
    v___x_1244_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_1241_, v_searcher_1242_, v___x_1243_);
    return v___x_1244_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0___boxed(
    mut v_s_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1246_: u8 = 0;
    let mut v_r_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v_s_1245_);
    leanh::lean_dec_ref(v_s_1245_);
    v_r_1247_ = leanh::lean_box((v_res_1246_) as usize);
    return v_r_1247_;
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
    mut v_escape_1248_: u8,
    mut v_s_1249_: *mut leanh::LeanObject,
    mut v_force_1250_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: u8 = 0;
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    let mut v___y_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u8 = 0;
    let mut v___x_1281_: u8 = 0;
    let mut v___x_1282_: u8 = 0;
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1285_: u8 = 0;
    let mut v___y_1287_: u32 = 0;
    let mut v___y_1288_: u8 = 0;
    let mut v___x_1289_: u32 = 0;
    let mut v___x_1290_: u8 = 0;
    let mut v___x_1291_: u8 = 0;
    let mut v___y_1293_: u32 = 0;
    let mut v___x_1294_: u32 = 0;
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1296_: u32 = 0;
    let mut v___x_1297_: u8 = 0;
    let mut v___y_1299_: u32 = 0;
    let mut v___x_1300_: u32 = 0;
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1302_: u32 = 0;
    let mut v___x_1303_: u8 = 0;
    let mut v___y_1305_: u8 = 0;
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: u32 = 0;
    let mut v_val_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u32 = 0;
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1323_: u8 = 0;
    let mut v___y_1325_: u8 = 0;
    let mut v___x_1326_: u8 = 0;
    let mut v___x_1327_: u8 = 0;
    let mut v___y_1329_: u8 = 0;
    let mut v___x_1330_: u8 = 0;
    let mut v___x_1331_: u8 = 0;
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: u8 = 0;
    let mut v___x_1335_: u8 = 0;
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_escape_1248_ == 0 {
                    return v_s_1249_;
                } else {
                    v___x_1316_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1317_ = lean_string_utf8_byte_size(v_s_1249_);
                    v___x_1318_ = lean_nat_dec_lt(v___x_1316_, v___x_1317_);
                    if v___x_1318_ == 0 {
                        v___x_1319_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
                        v___x_1320_ = lean_string_append(v___x_1319_, v_s_1249_);
                        leanh::lean_dec_ref(v_s_1249_);
                        v___x_1321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
                        v___x_1322_ = lean_string_append(v___x_1320_, v___x_1321_);
                        return v___x_1322_;
                    } else {
                        if v_force_1250_ == 0 {
                            v_c_1323_ = lean_string_get_byte_fast(v_s_1249_, v___x_1316_);
                            v___x_1334_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__8);
                            v___x_1335_ = lean_uint8_dec_le(v___x_1334_, v_c_1323_);
                            if v___x_1335_ == 0 {
                                v___y_1329_ = v___x_1335_;
                                state = 12;
                                continue;
                            } else {
                                v___x_1336_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__9);
                                v___x_1337_ = lean_uint8_dec_le(v_c_1323_, v___x_1336_);
                                v___y_1329_ = v___x_1337_;
                                state = 12;
                                continue;
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1252_ = leanh::lean_unsigned_to_nat(0);
                v___x_1253_ = lean_string_utf8_byte_size(v_s_1249_);
                leanh::lean_inc_ref(v_s_1249_);
                v___x_1254_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1254_, 0, v_s_1249_);
                leanh::lean_ctor_set(v___x_1254_, 1, v___x_1252_);
                leanh::lean_ctor_set(v___x_1254_, 2, v___x_1253_);
                v___x_1255_ = l_String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0(v___x_1254_);
                leanh::lean_dec_ref_known(v___x_1254_, 3);
                if v___x_1255_ == 0 {
                    v___x_1256_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__1);
                    v___x_1257_ = lean_string_append(v___x_1256_, v_s_1249_);
                    leanh::lean_dec_ref(v_s_1249_);
                    v___x_1258_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_escape___closed__2);
                    v___x_1259_ = lean_string_append(v___x_1257_, v___x_1258_);
                    return v___x_1259_;
                } else {
                    return v_s_1249_;
                }
            }
            2 => {
                v___x_1265_ = l_String_Slice_Pos_skipWhile___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__1(v___y_1262_, v___y_1261_);
                leanh::lean_dec_ref(v___y_1262_);
                v___x_1266_ = lean_nat_sub(v_endExclusive_1264_, v_startInclusive_1263_);
                leanh::lean_dec(v_startInclusive_1263_);
                leanh::lean_dec(v_endExclusive_1264_);
                v___x_1267_ = lean_nat_dec_eq(v___x_1265_, v___x_1266_);
                leanh::lean_dec(v___x_1266_);
                leanh::lean_dec(v___x_1265_);
                if v___x_1267_ == 0 {
                    state = 1;
                    continue;
                } else {
                    return v_s_1249_;
                }
            }
            3 => {
                v___x_1270_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscape___redArg___closed__3);
                v___x_1271_ = l_panic___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__2(v___x_1270_);
                v_startInclusive_1272_ = leanh::lean_ctor_get(v___x_1271_, 1);
                leanh::lean_inc(v_startInclusive_1272_);
                v_endExclusive_1273_ = leanh::lean_ctor_get(v___x_1271_, 2);
                leanh::lean_inc(v_endExclusive_1273_);
                v___y_1261_ = v___y_1269_;
                v___y_1262_ = v___x_1271_;
                v_startInclusive_1263_ = v_startInclusive_1272_;
                v_endExclusive_1264_ = v_endExclusive_1273_;
                state = 2;
                continue;
            }
            4 => {
                v___x_1275_ = leanh::lean_unsigned_to_nat(0);
                v___x_1276_ = lean_string_utf8_byte_size(v_s_1249_);
                leanh::lean_inc_ref(v_s_1249_);
                v___x_1277_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1277_, 0, v_s_1249_);
                leanh::lean_ctor_set(v___x_1277_, 1, v___x_1275_);
                leanh::lean_ctor_set(v___x_1277_, 2, v___x_1276_);
                v___x_1278_ = leanh::lean_unsigned_to_nat(1);
                v___x_1279_ = l_Substring_Raw_nextn(v___x_1277_, v___x_1278_, v___x_1275_);
                leanh::lean_dec_ref_known(v___x_1277_, 3);
                v___x_1280_ = lean_string_is_valid_pos(v_s_1249_, v___x_1279_);
                if v___x_1280_ == 0 {
                    leanh::lean_dec(v___x_1279_);
                    v___y_1269_ = v___x_1275_;
                    state = 3;
                    continue;
                } else {
                    v___x_1281_ = lean_string_is_valid_pos(v_s_1249_, v___x_1276_);
                    if v___x_1281_ == 0 {
                        leanh::lean_dec(v___x_1279_);
                        v___y_1269_ = v___x_1275_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1282_ = lean_nat_dec_le(v___x_1279_, v___x_1276_);
                        if v___x_1282_ == 0 {
                            leanh::lean_dec(v___x_1279_);
                            v___y_1269_ = v___x_1275_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_1279_);
                            leanh::lean_inc_ref(v_s_1249_);
                            v___x_1283_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_1283_, 0, v_s_1249_);
                            leanh::lean_ctor_set(v___x_1283_, 1, v___x_1279_);
                            leanh::lean_ctor_set(v___x_1283_, 2, v___x_1276_);
                            v___y_1261_ = v___x_1275_;
                            v___y_1262_ = v___x_1283_;
                            v_startInclusive_1263_ = v___x_1279_;
                            v_endExclusive_1264_ = v___x_1276_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v___y_1285_ == 0 {
                    state = 1;
                    continue;
                } else {
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v___y_1288_ == 0 {
                    v___x_1289_ = 95;
                    v___x_1290_ = lean_uint32_dec_eq(v___y_1287_, v___x_1289_);
                    if v___x_1290_ == 0 {
                        v___x_1291_ = l_Lean_isLetterLike(v___y_1287_);
                        v___y_1285_ = v___x_1291_;
                        state = 5;
                        continue;
                    } else {
                        v___y_1285_ = v___x_1290_;
                        state = 5;
                        continue;
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            7 => {
                v___x_1294_ = 97;
                v___x_1295_ = lean_uint32_dec_le(v___x_1294_, v___y_1293_);
                if v___x_1295_ == 0 {
                    v___y_1287_ = v___y_1293_;
                    v___y_1288_ = v___x_1295_;
                    state = 6;
                    continue;
                } else {
                    v___x_1296_ = 122;
                    v___x_1297_ = lean_uint32_dec_le(v___y_1293_, v___x_1296_);
                    v___y_1287_ = v___y_1293_;
                    v___y_1288_ = v___x_1297_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_1300_ = 65;
                v___x_1301_ = lean_uint32_dec_le(v___x_1300_, v___y_1299_);
                if v___x_1301_ == 0 {
                    v___y_1293_ = v___y_1299_;
                    state = 7;
                    continue;
                } else {
                    v___x_1302_ = 90;
                    v___x_1303_ = lean_uint32_dec_le(v___y_1299_, v___x_1302_);
                    if v___x_1303_ == 0 {
                        v___y_1293_ = v___y_1299_;
                        state = 7;
                        continue;
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            9 => {
                if v___y_1305_ == 0 {
                    v___x_1306_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1307_ = lean_string_utf8_byte_size(v_s_1249_);
                    leanh::lean_inc_ref(v_s_1249_);
                    v___x_1308_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1308_, 0, v_s_1249_);
                    leanh::lean_ctor_set(v___x_1308_, 1, v___x_1306_);
                    leanh::lean_ctor_set(v___x_1308_, 2, v___x_1307_);
                    v___x_1309_ = l_String_Slice_Pos_get_x3f(v___x_1308_, v___x_1306_);
                    leanh::lean_dec_ref_known(v___x_1308_, 3);
                    if leanh::lean_obj_tag(v___x_1309_) == 0 {
                        v___x_1310_ = 65;
                        v___y_1299_ = v___x_1310_;
                        state = 8;
                        continue;
                    } else {
                        v_val_1311_ = leanh::lean_ctor_get(v___x_1309_, 0);
                        leanh::lean_inc(v_val_1311_);
                        leanh::lean_dec_ref_known(v___x_1309_, 1);
                        v___x_1312_ = leanh::lean_unbox_uint32(v_val_1311_);
                        leanh::lean_dec(v_val_1311_);
                        v___y_1299_ = v___x_1312_;
                        state = 8;
                        continue;
                    }
                } else {
                    return v_s_1249_;
                }
            }
            10 => {
                v___x_1314_ = leanh::lean_unsigned_to_nat(1);
                v___x_1315_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(
                        v_s_1249_,
                        v___x_1314_,
                    );
                v___y_1305_ = v___x_1315_;
                state = 9;
                continue;
            }
            11 => {
                if v___y_1325_ == 0 {
                    v___x_1326_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__0);
                    v___x_1327_ = lean_uint8_dec_eq(v_c_1323_, v___x_1326_);
                    if v___x_1327_ == 0 {
                        v___y_1305_ = v___x_1327_;
                        state = 9;
                        continue;
                    } else {
                        state = 10;
                        continue;
                    }
                } else {
                    state = 10;
                    continue;
                }
            }
            12 => {
                if v___y_1329_ == 0 {
                    v___x_1330_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__6);
                    v___x_1331_ = lean_uint8_dec_le(v___x_1330_, v_c_1323_);
                    if v___x_1331_ == 0 {
                        v___y_1325_ = v___x_1331_;
                        state = 11;
                        continue;
                    } else {
                        v___x_1332_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest___closed__7);
                        v___x_1333_ = lean_uint8_dec_le(v_c_1323_, v___x_1332_);
                        v___y_1325_ = v___x_1333_;
                        state = 11;
                        continue;
                    }
                } else {
                    state = 10;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape___boxed(
    mut v_escape_1338_: *mut leanh::LeanObject,
    mut v_s_1339_: *mut leanh::LeanObject,
    mut v_force_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_escape_boxed_1341_: u8 = 0;
    let mut v_force_boxed_1342_: u8 = 0;
    let mut v_res_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_1341_ = (leanh::lean_unbox(v_escape_1338_) as u8);
    v_force_boxed_1342_ = (leanh::lean_unbox(v_force_1340_) as u8);
    v_res_1343_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
        v_escape_boxed_1341_,
        v_s_1339_,
        v_force_boxed_1342_,
    );
    return v_res_1343_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(
    mut v_s_1344_: *mut leanh::LeanObject,
    mut v_inst_1345_: *mut leanh::LeanObject,
    mut v_R_1346_: *mut leanh::LeanObject,
    mut v_a_1347_: *mut leanh::LeanObject,
    mut v_b_1348_: u8,
    mut v_c_1349_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1350_: u8 = 0;
    v___x_1350_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___redArg(v_s_1344_, v_a_1347_, v_b_1348_);
    return v___x_1350_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0___boxed(
    mut v_s_1351_: *mut leanh::LeanObject,
    mut v_inst_1352_: *mut leanh::LeanObject,
    mut v_R_1353_: *mut leanh::LeanObject,
    mut v_a_1354_: *mut leanh::LeanObject,
    mut v_b_1355_: *mut leanh::LeanObject,
    mut v_c_1356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1357_: u8 = 0;
    let mut v_res_1358_: u8 = 0;
    let mut v_r_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1357_ = (leanh::lean_unbox(v_b_1355_) as u8);
    v_res_1358_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape_spec__0_spec__0(v_s_1351_, v_inst_1352_, v_R_1353_, v_a_1354_, v_b_boxed_1357_, v_c_1356_);
    leanh::lean_dec_ref(v_s_1351_);
    v_r_1359_ = leanh::lean_box((v_res_1358_) as usize);
    return v_r_1359_;
}
pub unsafe fn l_Lean_Name_toStringWithSep___lam__0(
    mut v_x_1360_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1361_: u8 = 0;
    v___x_1361_ = 0;
    return v___x_1361_;
}
pub unsafe fn l_Lean_Name_toStringWithSep___lam__0___boxed(
    mut v_x_1362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1363_: u8 = 0;
    let mut v_r_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1363_ = l_Lean_Name_toStringWithSep___lam__0(v_x_1362_);
    leanh::lean_dec_ref(v_x_1362_);
    v_r_1364_ = leanh::lean_box((v_res_1363_) as usize);
    return v_r_1364_;
}
pub unsafe fn l_Lean_Name_toStringWithSep(
    mut v_sep_1367_: *mut leanh::LeanObject,
    mut v_escape_1368_: u8,
    mut v_n_1369_: *mut leanh::LeanObject,
    mut v_isToken_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_n_1369_) {
        0 => {
            let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_isToken_1370_);
            v___x_1371_ = l_Lean_Name_toStringWithSep___closed__0;
            return v___x_1371_;
        }
        1 => {
            let mut v_pre_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_1372_ = leanh::lean_ctor_get(v_n_1369_, 0);
            if leanh::lean_obj_tag(v_pre_1372_) == 0 {
                let mut v_str_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1375_: u8 = 0;
                let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_str_1373_ = leanh::lean_ctor_get(v_n_1369_, 1);
                leanh::lean_inc_ref_n(v_str_1373_, 2);
                leanh::lean_dec_ref_known(v_n_1369_, 2);
                v___x_1374_ = leanh::lean_apply_1(v_isToken_1370_, v_str_1373_);
                v___x_1375_ = (leanh::lean_unbox(v___x_1374_) as u8);
                v___x_1376_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_1368_,
                        v_str_1373_,
                        v___x_1375_,
                    );
                return v___x_1376_;
            } else {
                let mut v_str_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1380_: u8 = 0;
                let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_x27_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_pre_1372_);
                v_str_1377_ = leanh::lean_ctor_get(v_n_1369_, 1);
                leanh::lean_inc_ref_n(v_str_1377_, 2);
                leanh::lean_dec_ref_known(v_n_1369_, 2);
                leanh::lean_inc_ref(v_isToken_1370_);
                v_r_1378_ = l_Lean_Name_toStringWithSep(
                    v_sep_1367_,
                    v_escape_1368_,
                    v_pre_1372_,
                    v_isToken_1370_,
                );
                v___x_1379_ = lean_string_append(v_r_1378_, v_sep_1367_);
                v___x_1380_ = 0;
                v___x_1381_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_1368_,
                        v_str_1377_,
                        v___x_1380_,
                    );
                leanh::lean_inc_ref(v___x_1379_);
                v_r_x27_1382_ = lean_string_append(v___x_1379_, v___x_1381_);
                leanh::lean_dec_ref(v___x_1381_);
                if v_escape_1368_ == 0 {
                    leanh::lean_dec_ref(v___x_1379_);
                    leanh::lean_dec_ref(v_str_1377_);
                    leanh::lean_dec_ref(v_isToken_1370_);
                    return v_r_x27_1382_;
                } else {
                    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1384_: u8 = 0;
                    leanh::lean_inc_ref(v_r_x27_1382_);
                    v___x_1383_ = leanh::lean_apply_1(v_isToken_1370_, v_r_x27_1382_);
                    v___x_1384_ = (leanh::lean_unbox(v___x_1383_) as u8);
                    if v___x_1384_ == 0 {
                        leanh::lean_dec_ref(v___x_1379_);
                        leanh::lean_dec_ref(v_str_1377_);
                        return v_r_x27_1382_;
                    } else {
                        let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec_ref(v_r_x27_1382_);
                        v___x_1385_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(v_escape_1368_, v_str_1377_, v_escape_1368_);
                        v___x_1386_ = lean_string_append(v___x_1379_, v___x_1385_);
                        leanh::lean_dec_ref(v___x_1385_);
                        return v___x_1386_;
                    }
                }
            }
        }
        _ => {
            let mut v_pre_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_isToken_1370_);
            v_pre_1387_ = leanh::lean_ctor_get(v_n_1369_, 0);
            if leanh::lean_obj_tag(v_pre_1387_) == 0 {
                let mut v_i_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_i_1388_ = leanh::lean_ctor_get(v_n_1369_, 1);
                leanh::lean_inc(v_i_1388_);
                leanh::lean_dec_ref_known(v_n_1369_, 2);
                v___x_1389_ = l_Nat_reprFast(v_i_1388_);
                return v___x_1389_;
            } else {
                let mut v_i_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_pre_1387_);
                v_i_1390_ = leanh::lean_ctor_get(v_n_1369_, 1);
                leanh::lean_inc(v_i_1390_);
                leanh::lean_dec_ref_known(v_n_1369_, 2);
                v___f_1391_ = l_Lean_Name_toStringWithSep___closed__1;
                v___x_1392_ = l_Lean_Name_toStringWithSep(
                    v_sep_1367_,
                    v_escape_1368_,
                    v_pre_1387_,
                    v___f_1391_,
                );
                v___x_1393_ = lean_string_append(v___x_1392_, v_sep_1367_);
                v___x_1394_ = l_Nat_reprFast(v_i_1390_);
                v___x_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
                leanh::lean_dec_ref(v___x_1394_);
                return v___x_1395_;
            }
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithSep___boxed(
    mut v_sep_1396_: *mut leanh::LeanObject,
    mut v_escape_1397_: *mut leanh::LeanObject,
    mut v_n_1398_: *mut leanh::LeanObject,
    mut v_isToken_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_escape_boxed_1400_: u8 = 0;
    let mut v_res_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_1400_ = (leanh::lean_unbox(v_escape_1397_) as u8);
    v_res_1401_ = l_Lean_Name_toStringWithSep(
        v_sep_1396_,
        v_escape_boxed_1400_,
        v_n_1398_,
        v_isToken_1399_,
    );
    leanh::lean_dec_ref(v_sep_1396_);
    return v_res_1401_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2;
    v___x_1407_ = lean_string_utf8_byte_size(v___x_1406_);
    return v___x_1407_;
}
pub unsafe fn _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4;
    v___x_1410_ = lean_string_utf8_byte_size(v___x_1409_);
    return v___x_1410_;
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(
    mut v_n_1411_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: u8 = 0;
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: u8 = 0;
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: u8 = 0;
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: u8 = 0;
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1412_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__1;
                v___x_1413_ = lean_name_eq(v_n_1411_, v___x_1412_);
                v___x_1414_ = 1;
                if v___x_1413_ == 0 {
                    v___x_1415_ = l_Lean_Name_getRoot(v_n_1411_);
                    if leanh::lean_obj_tag(v___x_1415_) == 1 {
                        v_str_1416_ = leanh::lean_ctor_get(v___x_1415_, 1);
                        leanh::lean_inc_ref(v_str_1416_);
                        leanh::lean_dec_ref_known(v___x_1415_, 2);
                        v___x_1424_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__4;
                        v___x_1425_ = lean_string_utf8_byte_size(v_str_1416_);
                        v___x_1426_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__5);
                        v___x_1427_ = lean_nat_dec_le(v___x_1426_, v___x_1425_);
                        if v___x_1427_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_1428_ = leanh::lean_unsigned_to_nat(0);
                            v___x_1429_ = lean_string_memcmp(
                                v_str_1416_,
                                v___x_1424_,
                                v___x_1428_,
                                v___x_1428_,
                                v___x_1426_,
                            );
                            if v___x_1429_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_str_1416_);
                                return v___x_1414_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1415_);
                        return v___x_1413_;
                    }
                } else {
                    return v___x_1414_;
                }
            }
            1 => {
                v___x_1418_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__2;
                v___x_1419_ = lean_string_utf8_byte_size(v_str_1416_);
                v___x_1420_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3_once), _init_l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___closed__3);
                v___x_1421_ = lean_nat_dec_le(v___x_1420_, v___x_1419_);
                if v___x_1421_ == 0 {
                    leanh::lean_dec_ref(v_str_1416_);
                    return v___x_1413_;
                } else {
                    v___x_1422_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1423_ = lean_string_memcmp(
                        v_str_1416_,
                        v___x_1418_,
                        v___x_1422_,
                        v___x_1422_,
                        v___x_1420_,
                    );
                    leanh::lean_dec_ref(v_str_1416_);
                    return v___x_1423_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax___boxed(
    mut v_n_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1431_: u8 = 0;
    let mut v_r_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1431_ =
        l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(
            v_n_1430_,
        );
    leanh::lean_dec(v_n_1430_);
    v_r_1432_ = leanh::lean_box((v_res_1431_) as usize);
    return v_r_1432_;
}
pub unsafe fn l_Lean_Name_toStringWithToken(
    mut v_n_1434_: *mut leanh::LeanObject,
    mut v_escape_1435_: u8,
    mut v_isToken_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ = l_Lean_Name_toStringWithToken___closed__0;
    if v_escape_1435_ == 0 {
        let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1438_ =
            l_Lean_Name_toStringWithSep(v___x_1437_, v_escape_1435_, v_n_1434_, v_isToken_1436_);
        return v___x_1438_;
    } else {
        let mut v___x_1439_: u8 = 0;
        leanh::lean_inc(v_n_1434_);
        v___x_1439_ = lean_is_inaccessible_user_name(v_n_1434_);
        if v___x_1439_ == 0 {
            let mut v___x_1440_: u8 = 0;
            v___x_1440_ = l_Lean_Name_hasMacroScopes(v_n_1434_);
            if v___x_1440_ == 0 {
                let mut v___x_1441_: u8 = 0;
                v___x_1441_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_1434_);
                if v___x_1441_ == 0 {
                    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1442_ = l_Lean_Name_toStringWithSep(
                        v___x_1437_,
                        v_escape_1435_,
                        v_n_1434_,
                        v_isToken_1436_,
                    );
                    return v___x_1442_;
                } else {
                    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1443_ = l_Lean_Name_toStringWithSep(
                        v___x_1437_,
                        v___x_1440_,
                        v_n_1434_,
                        v_isToken_1436_,
                    );
                    return v___x_1443_;
                }
            } else {
                let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1444_ = l_Lean_Name_toStringWithSep(
                    v___x_1437_,
                    v___x_1439_,
                    v_n_1434_,
                    v_isToken_1436_,
                );
                return v___x_1444_;
            }
        } else {
            let mut v___x_1445_: u8 = 0;
            let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1445_ = 0;
            v___x_1446_ =
                l_Lean_Name_toStringWithSep(v___x_1437_, v___x_1445_, v_n_1434_, v_isToken_1436_);
            return v___x_1446_;
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithToken___boxed(
    mut v_n_1447_: *mut leanh::LeanObject,
    mut v_escape_1448_: *mut leanh::LeanObject,
    mut v_isToken_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_escape_boxed_1450_: u8 = 0;
    let mut v_res_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_1450_ = (leanh::lean_unbox(v_escape_1448_) as u8);
    v_res_1451_ = l_Lean_Name_toStringWithToken(v_n_1447_, v_escape_boxed_1450_, v_isToken_1449_);
    return v_res_1451_;
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(
    mut v_sep_1452_: *mut leanh::LeanObject,
    mut v_escape_1453_: u8,
    mut v_n_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_n_1454_) {
        0 => {
            let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1455_ = l_Lean_Name_toStringWithSep___closed__0;
            return v___x_1455_;
        }
        1 => {
            let mut v_pre_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_1456_ = leanh::lean_ctor_get(v_n_1454_, 0);
            if leanh::lean_obj_tag(v_pre_1456_) == 0 {
                let mut v_str_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1458_: u8 = 0;
                let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_str_1457_ = leanh::lean_ctor_get(v_n_1454_, 1);
                leanh::lean_inc_ref(v_str_1457_);
                leanh::lean_dec_ref_known(v_n_1454_, 2);
                v___x_1458_ = 0;
                v___x_1459_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_1453_,
                        v_str_1457_,
                        v___x_1458_,
                    );
                return v___x_1459_;
            } else {
                let mut v_str_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1463_: u8 = 0;
                let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_x27_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_pre_1456_);
                v_str_1460_ = leanh::lean_ctor_get(v_n_1454_, 1);
                leanh::lean_inc_ref(v_str_1460_);
                leanh::lean_dec_ref_known(v_n_1454_, 2);
                v_r_1461_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_1452_, v_escape_1453_, v_pre_1456_);
                v___x_1462_ = lean_string_append(v_r_1461_, v_sep_1452_);
                v___x_1463_ = 0;
                v___x_1464_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_1453_,
                        v_str_1460_,
                        v___x_1463_,
                    );
                v_r_x27_1465_ = lean_string_append(v___x_1462_, v___x_1464_);
                leanh::lean_dec_ref(v___x_1464_);
                return v_r_x27_1465_;
            }
        }
        _ => {
            let mut v_pre_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_1466_ = leanh::lean_ctor_get(v_n_1454_, 0);
            if leanh::lean_obj_tag(v_pre_1466_) == 0 {
                let mut v_i_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_i_1467_ = leanh::lean_ctor_get(v_n_1454_, 1);
                leanh::lean_inc(v_i_1467_);
                leanh::lean_dec_ref_known(v_n_1454_, 2);
                v___x_1468_ = l_Nat_reprFast(v_i_1467_);
                return v___x_1468_;
            } else {
                let mut v_i_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_pre_1466_);
                v_i_1469_ = leanh::lean_ctor_get(v_n_1454_, 1);
                leanh::lean_inc(v_i_1469_);
                leanh::lean_dec_ref_known(v_n_1454_, 2);
                v___x_1470_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_1452_, v_escape_1453_, v_pre_1466_);
                v___x_1471_ = lean_string_append(v___x_1470_, v_sep_1452_);
                v___x_1472_ = l_Nat_reprFast(v_i_1469_);
                v___x_1473_ = lean_string_append(v___x_1471_, v___x_1472_);
                leanh::lean_dec_ref(v___x_1472_);
                return v___x_1473_;
            }
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0___boxed(
    mut v_sep_1474_: *mut leanh::LeanObject,
    mut v_escape_1475_: *mut leanh::LeanObject,
    mut v_n_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_escape_boxed_1477_: u8 = 0;
    let mut v_res_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_1477_ = (leanh::lean_unbox(v_escape_1475_) as u8);
    v_res_1478_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v_sep_1474_, v_escape_boxed_1477_, v_n_1476_);
    leanh::lean_dec_ref(v_sep_1474_);
    return v_res_1478_;
}
pub unsafe fn l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
    mut v_n_1479_: *mut leanh::LeanObject,
    mut v_escape_1480_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1481_ = l_Lean_Name_toStringWithToken___closed__0;
    if v_escape_1480_ == 0 {
        let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1482_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_1481_, v_escape_1480_, v_n_1479_);
        return v___x_1482_;
    } else {
        let mut v___x_1483_: u8 = 0;
        leanh::lean_inc(v_n_1479_);
        v___x_1483_ = lean_is_inaccessible_user_name(v_n_1479_);
        if v___x_1483_ == 0 {
            let mut v___x_1484_: u8 = 0;
            v___x_1484_ = l_Lean_Name_hasMacroScopes(v_n_1479_);
            if v___x_1484_ == 0 {
                let mut v___x_1485_: u8 = 0;
                v___x_1485_ = l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithToken_maybePseudoSyntax(v_n_1479_);
                if v___x_1485_ == 0 {
                    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1486_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_1481_, v_escape_1480_, v_n_1479_);
                    return v___x_1486_;
                } else {
                    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1487_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_1481_, v___x_1484_, v_n_1479_);
                    return v___x_1487_;
                }
            } else {
                let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1488_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_1481_, v___x_1483_, v_n_1479_);
                return v___x_1488_;
            }
        } else {
            let mut v___x_1489_: u8 = 0;
            let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1489_ = 0;
            v___x_1490_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0_spec__0(v___x_1481_, v___x_1489_, v_n_1479_);
            return v___x_1490_;
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0___boxed(
    mut v_n_1491_: *mut leanh::LeanObject,
    mut v_escape_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_escape_boxed_1493_: u8 = 0;
    let mut v_res_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_1493_ = (leanh::lean_unbox(v_escape_1492_) as u8);
    v_res_1494_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_n_1491_,
        v_escape_boxed_1493_,
    );
    return v_res_1494_;
}
pub unsafe fn l_Lean_Name_toString(
    mut v_n_1495_: *mut leanh::LeanObject,
    mut v_escape_1496_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_n_1495_,
        v_escape_1496_,
    );
    return v___x_1497_;
}
pub unsafe fn l_Lean_Name_toString___boxed(
    mut v_n_1498_: *mut leanh::LeanObject,
    mut v_escape_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_escape_boxed_1500_: u8 = 0;
    let mut v_res_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_1500_ = (leanh::lean_unbox(v_escape_1499_) as u8);
    v_res_1501_ = l_Lean_Name_toString(v_n_1498_, v_escape_boxed_1500_);
    return v_res_1501_;
}
pub unsafe fn l_Lean_Name_instToString___lam__0(
    mut v_n_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = 1;
    v___x_1504_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1502_, v___x_1503_);
    return v___x_1504_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ToString_Name(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Substring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_ToString_Name(
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
pub unsafe fn initialize_Init_Data_ToString_Name(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Substring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_ToString_Name(builtin);
}