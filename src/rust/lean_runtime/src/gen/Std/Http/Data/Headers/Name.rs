// Lean compiler output
// Module: Std.Http.Data.Headers.Name
// Imports: Init.Data.ToString Std.Http.Internal Init.Data.String.Search Init.Data.String.Iter
use crate::r#gen::Init::Data::Repr::l_String_quote;
use crate::r#gen::Init::Data::String::Iter::{
    initialize_Init_Data_String_Iter, runtime_initialize_Init_Data_String_Iter,
};
use crate::r#gen::Init::Data::String::Pattern::Char::l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    l_String_Slice_splitToSubslice___redArg, l_String_Slice_toString, l_String_Slice_trimAscii,
};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Prelude::{
    l_Char_utf8Size, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom, l_String_decEq___boxed,
    l_String_hash___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Std::Http::Internal::LowerCase::l_Std_Http_Internal_instDecidableIsLowerCase;
use crate::r#gen::Std::Http::Internal::String::l_Std_Http_Internal_isToken;
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint32_add;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint32_dec_le,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_4, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__3_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__3_value)
        as *mut LeanObject;
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__3_value)
            as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__6_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__6_value)
        as *mut LeanObject;
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_1:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_2:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__6_value)
            as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__8_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__8_value)
            as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [100, 101, 99, 105, 100, 101, 0],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10_value)
        as *mut LeanObject;
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_1:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_2:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10_value
        ) as *mut LeanObject,
        14249328086033210933 as *mut LeanObject,
    ],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11_value)
        as *mut LeanObject;
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__14_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__14_value)
        as *mut LeanObject;
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_1:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_2:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value:
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
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__14_value
        ) as *mut LeanObject,
        3488656302031949961 as *mut LeanObject,
    ],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__16_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__16_value)
        as *mut LeanObject;
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Header_Name_isValidHeaderValue___autoParam: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Header_Name_isLowerCase___autoParam: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [123, 32, 0],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [118, 97, 108, 117, 101, 0],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__4_value: LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__8_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [44, 0],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__10_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            105, 115, 86, 97, 108, 105, 100, 72, 101, 97, 100, 101, 114, 86, 97, 108, 117, 101, 0,
        ],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Header_instReprName_repr___redArg___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__12_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [95, 0],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Header_instReprName_repr___redArg___closed__12_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__14_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 115, 76, 111, 119, 101, 114, 67, 97, 115, 101, 0],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Header_instReprName_repr___redArg___closed__14_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__16_value: LeanStringObject<3> =
    LeanStringObject {
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
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__16_value)
        as *mut LeanObject;
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__19_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName_repr___redArg___closed__20_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Header_instReprName_repr___redArg___closed__16_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Header_instReprName_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__20_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_instReprName___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Header_instReprName_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_instReprName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_instReprName: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_instBEq___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_String_decEq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_Name_instBEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_instBEq: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_instBEq___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_instHashable___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_String_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_Name_instHashable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_instHashable___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_instHashable: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_instHashable___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_instInhabited: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprName_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_ofString_x21___closed__0_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 72, 101, 97, 100, 101,
            114, 115, 46, 78, 97, 109, 101, 0,
        ],
    };
static mut l_Std_Http_Header_Name_ofString_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_ofString_x21___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_ofString_x21___closed__1_value: LeanStringObject<31> =
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 72, 101, 97, 100, 101, 114, 46, 78, 97, 109,
            101, 46, 111, 102, 83, 116, 114, 105, 110, 103, 33, 0,
        ],
    };
static mut l_Std_Http_Header_Name_ofString_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_ofString_x21___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_ofString_x21___closed__2_value: LeanStringObject<22> =
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
            105, 110, 118, 97, 108, 105, 100, 32, 104, 101, 97, 100, 101, 114, 32, 110, 97, 109,
            101, 58, 32, 0,
        ],
    };
static mut l_Std_Http_Header_Name_ofString_x21___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_ofString_x21___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_toCanonical___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Http_Header_Name_toCanonical___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_toCanonical___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_toCanonical___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [45, 0],
    };
static mut l_Std_Http_Header_Name_toCanonical___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_toCanonical___closed__1_value) as *mut LeanObject;
static mut l_Std_Http_Header_Name_toCanonical___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Name_toCanonical___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Header_Name_toCanonical___closed__3_value: LeanStringObject<1> =
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
static mut l_Std_Http_Header_Name_toCanonical___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_toCanonical___closed__3_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Header_Name_instToString___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_Name_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_instToString___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_contentType___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [99, 111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101, 0],
    };
static mut l_Std_Http_Header_Name_contentType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_contentType___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_contentType: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_contentType___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_contentLength___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            99, 111, 110, 116, 101, 110, 116, 45, 108, 101, 110, 103, 116, 104, 0,
        ],
    };
static mut l_Std_Http_Header_Name_contentLength___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_contentLength___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_contentLength: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_contentLength___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_host___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 111, 115, 116, 0],
};
static mut l_Std_Http_Header_Name_host___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_host___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_host: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_host___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_authorization___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
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
            97, 117, 116, 104, 111, 114, 105, 122, 97, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Std_Http_Header_Name_authorization___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_authorization___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_authorization: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_authorization___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_userAgent___closed__0_value: LeanStringObject<11> =
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
        m_data: [117, 115, 101, 114, 45, 97, 103, 101, 110, 116, 0],
    };
static mut l_Std_Http_Header_Name_userAgent___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_userAgent___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_userAgent: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_userAgent___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_accept___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [97, 99, 99, 101, 112, 116, 0],
    };
static mut l_Std_Http_Header_Name_accept___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_accept___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_accept: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_accept___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_connection___closed__0_value: LeanStringObject<11> =
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
        m_data: [99, 111, 110, 110, 101, 99, 116, 105, 111, 110, 0],
    };
static mut l_Std_Http_Header_Name_connection___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_connection___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_connection: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_connection___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_transferEncoding___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            116, 114, 97, 110, 115, 102, 101, 114, 45, 101, 110, 99, 111, 100, 105, 110, 103, 0,
        ],
    };
static mut l_Std_Http_Header_Name_transferEncoding___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_transferEncoding___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_transferEncoding: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_transferEncoding___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Header_Name_server___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [115, 101, 114, 118, 101, 114, 0],
    };
static mut l_Std_Http_Header_Name_server___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_server___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_server: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_server___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_date___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 97, 116, 101, 0],
};
static mut l_Std_Http_Header_Name_date___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_date___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_date: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_date___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Header_Name_expect___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [101, 120, 112, 101, 99, 116, 0],
    };
static mut l_Std_Http_Header_Name_expect___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_expect___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Header_Name_expect: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Name_expect___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12()
-> *mut LeanObject {
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    v___x_392_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__10;
    v___x_393_ = l_Lean_mkAtom(v___x_392_);
    return v___x_393_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13()
-> *mut LeanObject {
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    v___x_394_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__12,
    );
    v___x_395_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5;
    v___x_396_ = lean_array_push(v___x_395_, v___x_394_);
    return v___x_396_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17()
-> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__16;
    v___x_408_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5;
    v___x_409_ = lean_array_push(v___x_408_, v___x_407_);
    return v___x_409_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18()
-> *mut LeanObject {
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    v___x_410_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__17,
    );
    v___x_411_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__15;
    v___x_412_ = lean_box(2);
    v___x_413_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_413_, 0, v___x_412_);
    lean_ctor_set(v___x_413_, 1, v___x_411_);
    lean_ctor_set(v___x_413_, 2, v___x_410_);
    return v___x_413_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19()
-> *mut LeanObject {
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v___x_414_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__18,
    );
    v___x_415_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__13,
    );
    v___x_416_ = lean_array_push(v___x_415_, v___x_414_);
    return v___x_416_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20()
-> *mut LeanObject {
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    v___x_417_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__19,
    );
    v___x_418_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__11;
    v___x_419_ = lean_box(2);
    v___x_420_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_420_, 0, v___x_419_);
    lean_ctor_set(v___x_420_, 1, v___x_418_);
    lean_ctor_set(v___x_420_, 2, v___x_417_);
    return v___x_420_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21()
-> *mut LeanObject {
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    v___x_421_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__20,
    );
    v___x_422_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5;
    v___x_423_ = lean_array_push(v___x_422_, v___x_421_);
    return v___x_423_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22()
-> *mut LeanObject {
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    v___x_424_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__21,
    );
    v___x_425_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__9;
    v___x_426_ = lean_box(2);
    v___x_427_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_427_, 0, v___x_426_);
    lean_ctor_set(v___x_427_, 1, v___x_425_);
    lean_ctor_set(v___x_427_, 2, v___x_424_);
    return v___x_427_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23()
-> *mut LeanObject {
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v___x_428_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__22,
    );
    v___x_429_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5;
    v___x_430_ = lean_array_push(v___x_429_, v___x_428_);
    return v___x_430_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24()
-> *mut LeanObject {
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    v___x_431_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__23,
    );
    v___x_432_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__7;
    v___x_433_ = lean_box(2);
    v___x_434_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_434_, 0, v___x_433_);
    lean_ctor_set(v___x_434_, 1, v___x_432_);
    lean_ctor_set(v___x_434_, 2, v___x_431_);
    return v___x_434_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25()
-> *mut LeanObject {
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    v___x_435_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__24,
    );
    v___x_436_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__5;
    v___x_437_ = lean_array_push(v___x_436_, v___x_435_);
    return v___x_437_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26()
-> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__25,
    );
    v___x_439_ = l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__4;
    v___x_440_ = lean_box(2);
    v___x_441_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_441_, 0, v___x_440_);
    lean_ctor_set(v___x_441_, 1, v___x_439_);
    lean_ctor_set(v___x_441_, 2, v___x_438_);
    return v___x_441_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam() -> *mut LeanObject {
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    v___x_442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26,
    );
    return v___x_442_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_isLowerCase___autoParam() -> *mut LeanObject {
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v___x_443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26_once
        ),
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam___closed__26,
    );
    return v___x_443_;
}
pub unsafe fn l_Nat_cast___at___00Std_Http_Header_instReprName_repr_spec__0(
    mut v_a_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = lean_nat_to_int(v_a_444_);
    return v___x_445_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprName_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    v___x_459_ = lean_unsigned_to_nat(9);
    v___x_460_ = lean_nat_to_int(v___x_459_);
    return v___x_460_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprName_repr___redArg___closed__17() -> *mut LeanObject {
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v___x_474_ = l_Std_Http_Header_instReprName_repr___redArg___closed__0;
    v___x_475_ = lean_string_length(v___x_474_);
    return v___x_475_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprName_repr___redArg___closed__18() -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprName_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprName_repr___redArg___closed__17_once),
        _init_l_Std_Http_Header_instReprName_repr___redArg___closed__17,
    );
    v___x_477_ = lean_nat_to_int(v___x_476_);
    return v___x_477_;
}
pub unsafe fn l_Std_Http_Header_instReprName_repr___redArg(
    mut v_x_482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: u8 = 0;
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    v___x_483_ = l_Std_Http_Header_instReprName_repr___redArg___closed__5;
    v___x_484_ = l_Std_Http_Header_instReprName_repr___redArg___closed__6;
    v___x_485_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprName_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprName_repr___redArg___closed__7_once),
        _init_l_Std_Http_Header_instReprName_repr___redArg___closed__7,
    );
    v___x_486_ = l_String_quote(v_x_482_);
    v___x_487_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_487_, 0, v___x_486_);
    v___x_488_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_488_, 0, v___x_485_);
    lean_ctor_set(v___x_488_, 1, v___x_487_);
    v___x_489_ = 0;
    v___x_490_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_490_, 0, v___x_488_);
    lean_ctor_set_uint8(
        v___x_490_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_489_,
    );
    v___x_491_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_491_, 0, v___x_484_);
    lean_ctor_set(v___x_491_, 1, v___x_490_);
    v___x_492_ = l_Std_Http_Header_instReprName_repr___redArg___closed__9;
    v___x_493_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_493_, 0, v___x_491_);
    lean_ctor_set(v___x_493_, 1, v___x_492_);
    v___x_494_ = lean_box(1);
    v___x_495_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_495_, 0, v___x_493_);
    lean_ctor_set(v___x_495_, 1, v___x_494_);
    v___x_496_ = l_Std_Http_Header_instReprName_repr___redArg___closed__11;
    v___x_497_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_497_, 0, v___x_495_);
    lean_ctor_set(v___x_497_, 1, v___x_496_);
    v___x_498_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_498_, 0, v___x_497_);
    lean_ctor_set(v___x_498_, 1, v___x_483_);
    v___x_499_ = l_Std_Http_Header_instReprName_repr___redArg___closed__13;
    v___x_500_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_500_, 0, v___x_498_);
    lean_ctor_set(v___x_500_, 1, v___x_499_);
    v___x_501_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_501_, 0, v___x_500_);
    lean_ctor_set(v___x_501_, 1, v___x_492_);
    v___x_502_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_502_, 0, v___x_501_);
    lean_ctor_set(v___x_502_, 1, v___x_494_);
    v___x_503_ = l_Std_Http_Header_instReprName_repr___redArg___closed__15;
    v___x_504_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_504_, 0, v___x_502_);
    lean_ctor_set(v___x_504_, 1, v___x_503_);
    v___x_505_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_505_, 0, v___x_504_);
    lean_ctor_set(v___x_505_, 1, v___x_483_);
    v___x_506_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_506_, 0, v___x_505_);
    lean_ctor_set(v___x_506_, 1, v___x_499_);
    v___x_507_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprName_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprName_repr___redArg___closed__18_once),
        _init_l_Std_Http_Header_instReprName_repr___redArg___closed__18,
    );
    v___x_508_ = l_Std_Http_Header_instReprName_repr___redArg___closed__19;
    v___x_509_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_509_, 0, v___x_508_);
    lean_ctor_set(v___x_509_, 1, v___x_506_);
    v___x_510_ = l_Std_Http_Header_instReprName_repr___redArg___closed__20;
    v___x_511_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_511_, 0, v___x_509_);
    lean_ctor_set(v___x_511_, 1, v___x_510_);
    v___x_512_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_512_, 0, v___x_507_);
    lean_ctor_set(v___x_512_, 1, v___x_511_);
    v___x_513_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_513_, 0, v___x_512_);
    lean_ctor_set_uint8(
        v___x_513_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_489_,
    );
    return v___x_513_;
}
pub unsafe fn l_Std_Http_Header_instReprName_repr(
    mut v_x_514_: *mut LeanObject,
    mut v_prec_515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = l_Std_Http_Header_instReprName_repr___redArg(v_x_514_);
    return v___x_516_;
}
pub unsafe fn l_Std_Http_Header_instReprName_repr___boxed(
    mut v_x_517_: *mut LeanObject,
    mut v_prec_518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_519_: *mut LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Std_Http_Header_instReprName_repr(v_x_517_, v_prec_518_);
    lean_dec(v_prec_518_);
    return v_res_519_;
}
pub unsafe fn l_Std_Http_Header_instDecidableEqName_decEq(
    mut v_x_522_: *mut LeanObject,
    mut v_x_523_: *mut LeanObject,
) -> u8 {
    let mut v___x_524_: u8 = 0;
    v___x_524_ = lean_string_dec_eq(v_x_522_, v_x_523_);
    return v___x_524_;
}
pub unsafe fn l_Std_Http_Header_instDecidableEqName_decEq___boxed(
    mut v_x_525_: *mut LeanObject,
    mut v_x_526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_527_: u8 = 0;
    let mut v_r_528_: *mut LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Std_Http_Header_instDecidableEqName_decEq(v_x_525_, v_x_526_);
    lean_dec_ref(v_x_526_);
    lean_dec_ref(v_x_525_);
    v_r_528_ = lean_box((v_res_527_) as usize);
    return v_r_528_;
}
pub unsafe fn l_Std_Http_Header_instDecidableEqName(
    mut v_x_529_: *mut LeanObject,
    mut v_x_530_: *mut LeanObject,
) -> u8 {
    let mut v___x_531_: u8 = 0;
    v___x_531_ = lean_string_dec_eq(v_x_529_, v_x_530_);
    return v___x_531_;
}
pub unsafe fn l_Std_Http_Header_instDecidableEqName___boxed(
    mut v_x_532_: *mut LeanObject,
    mut v_x_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_534_: u8 = 0;
    let mut v_r_535_: *mut LeanObject = core::ptr::null_mut();
    v_res_534_ = l_Std_Http_Header_instDecidableEqName(v_x_532_, v_x_533_);
    lean_dec_ref(v_x_533_);
    lean_dec_ref(v_x_532_);
    v_r_535_ = lean_box((v_res_534_) as usize);
    return v_r_535_;
}
pub unsafe fn l_String_mapAux___at___00Std_Http_Header_Name_ofString_x3f_spec__0(
    mut v_s_541_: *mut LeanObject,
    mut v_p_542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_544_: u32 = 0;
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: u32 = 0;
    let mut v___x_552_: u32 = 0;
    let mut v___x_553_: u8 = 0;
    let mut v___x_554_: u32 = 0;
    let mut v___x_555_: u8 = 0;
    let mut v___x_556_: u32 = 0;
    let mut v___x_557_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_549_ = lean_string_utf8_byte_size(v_s_541_);
                v___x_550_ = lean_nat_dec_eq(v_p_542_, v___x_549_);
                if v___x_550_ == 0 {
                    v___x_551_ = lean_string_utf8_get_fast(v_s_541_, v_p_542_);
                    v___x_552_ = 65;
                    v___x_553_ = lean_uint32_dec_le(v___x_552_, v___x_551_);
                    if v___x_553_ == 0 {
                        v___y_544_ = v___x_551_;
                        state = 1;
                        continue;
                    } else {
                        v___x_554_ = 90;
                        v___x_555_ = lean_uint32_dec_le(v___x_551_, v___x_554_);
                        if v___x_555_ == 0 {
                            v___y_544_ = v___x_551_;
                            state = 1;
                            continue;
                        } else {
                            v___x_556_ = 32;
                            v___x_557_ = lean_uint32_add(v___x_551_, v___x_556_);
                            v___y_544_ = v___x_557_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_p_542_);
                    return v_s_541_;
                }
            }
            1 => {
                lean_inc(v_p_542_);
                v___x_545_ = lean_string_utf8_set(v_s_541_, v_p_542_, v___y_544_);
                v___x_546_ = l_Char_utf8Size(v___y_544_);
                v___x_547_ = lean_nat_add(v_p_542_, v___x_546_);
                lean_dec(v___x_546_);
                lean_dec(v_p_542_);
                v_s_541_ = v___x_545_;
                v_p_542_ = v___x_547_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_Name_ofString_x3f(
    mut v_s_558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u8 = 0;
    let mut v___x_566_: u8 = 0;
    v___x_559_ = lean_unsigned_to_nat(0);
    v___x_560_ = lean_string_utf8_byte_size(v_s_558_);
    v___x_561_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_561_, 0, v_s_558_);
    lean_ctor_set(v___x_561_, 1, v___x_559_);
    lean_ctor_set(v___x_561_, 2, v___x_560_);
    v___x_562_ = l_String_Slice_trimAscii(v___x_561_);
    v___x_563_ = l_String_Slice_toString(v___x_562_);
    lean_dec_ref(v___x_562_);
    v_val_564_ =
        l_String_mapAux___at___00Std_Http_Header_Name_ofString_x3f_spec__0(v___x_563_, v___x_559_);
    lean_inc_ref_n(v_val_564_, 2);
    v___x_565_ = l_Std_Http_Internal_instDecidableIsLowerCase(v_val_564_);
    v___x_566_ = l_Std_Http_Internal_isToken(v_val_564_);
    if v___x_566_ == 0 {
        let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_val_564_);
        v___x_567_ = lean_box(0);
        return v___x_567_;
    } else {
        if v___x_565_ == 0 {
            let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_val_564_);
            v___x_568_ = lean_box(0);
            return v___x_568_;
        } else {
            let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
            v___x_569_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_569_, 0, v_val_564_);
            return v___x_569_;
        }
    }
}
pub unsafe fn l_panic___at___00Std_Http_Header_Name_ofString_x21_spec__0(
    mut v_msg_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    v___x_571_ = l_Std_Http_Header_instReprName_repr___redArg___closed__12;
    v___x_572_ = lean_panic_fn_borrowed(v___x_571_, v_msg_570_);
    return v___x_572_;
}
pub unsafe fn l_Std_Http_Header_Name_ofString_x21(
    mut v_s_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_s_576_);
    v___x_577_ = l_Std_Http_Header_Name_ofString_x3f(v_s_576_);
    if lean_obj_tag(v___x_577_) == 0 {
        let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
        v___x_578_ = l_Std_Http_Header_Name_ofString_x21___closed__0;
        v___x_579_ = l_Std_Http_Header_Name_ofString_x21___closed__1;
        v___x_580_ = lean_unsigned_to_nat(102);
        v___x_581_ = lean_unsigned_to_nat(12);
        v___x_582_ = l_Std_Http_Header_Name_ofString_x21___closed__2;
        v___x_583_ = l_String_quote(v_s_576_);
        v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
        lean_dec_ref(v___x_583_);
        v___x_585_ =
            l_mkPanicMessageWithDecl(v___x_578_, v___x_579_, v___x_580_, v___x_581_, v___x_584_);
        lean_dec_ref(v___x_584_);
        v___x_586_ = l_panic___at___00Std_Http_Header_Name_ofString_x21_spec__0(v___x_585_);
        return v___x_586_;
    } else {
        let mut v_val_587_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_576_);
        v_val_587_ = lean_ctor_get(v___x_577_, 0);
        lean_inc(v_val_587_);
        lean_dec_ref_known(v___x_577_, 1);
        return v_val_587_;
    }
}
pub unsafe fn l_Std_Http_Header_Name_toCanonical___lam__0(
    mut v___x_588_: *mut LeanObject,
    mut v___x_589_: *mut LeanObject,
    mut v___x_590_: *mut LeanObject,
    mut v_name_591_: *mut LeanObject,
    mut v___x_592_: *mut LeanObject,
    mut v___x_593_: *mut LeanObject,
    mut v_it_594_: *mut LeanObject,
    mut v_acc_595_: *mut LeanObject,
    mut v_hP_596_: *mut LeanObject,
    mut v_recur_597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_606_: u8 = 0;
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut v_it_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: u32 = 0;
    let mut v___x_622_: u32 = 0;
    let mut v___x_623_: u8 = 0;
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u32 = 0;
    let mut v___x_626_: u8 = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u32 = 0;
    let mut v___x_629_: u32 = 0;
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_635_: u8 = 0;
    let mut v___x_636_: u8 = 0;
    let mut v___x_637_: u32 = 0;
    let mut v___x_638_: u32 = 0;
    let mut v___x_639_: u8 = 0;
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_it_594_) == 0 {
                    v_currPos_631_ = lean_ctor_get(v_it_594_, 0);
                    v_searcher_632_ = lean_ctor_get(v_it_594_, 1);
                    v_isSharedCheck_655_ = (!lean_is_exclusive(v_it_594_)) as u8;
                    if v_isSharedCheck_655_ == 0 {
                        v___x_634_ = v_it_594_;
                        v_isShared_635_ = v_isSharedCheck_655_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_searcher_632_);
                        lean_inc(v_currPos_631_);
                        lean_dec(v_it_594_);
                        v___x_634_ = lean_box(0);
                        v_isShared_635_ = v_isSharedCheck_655_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_recur_597_);
                    lean_dec(v___x_592_);
                    return v_acc_595_;
                }
            }
            1 => {
                if lean_obj_tag(v_acc_595_) == 0 {
                    v___x_601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_601_, 0, v_out_600_);
                    v___x_602_ = lean_apply_4(
                        v_recur_597_,
                        v_it_599_,
                        v___x_601_,
                        lean_box(0),
                        lean_box(0),
                    );
                    return v___x_602_;
                } else {
                    v_val_603_ = lean_ctor_get(v_acc_595_, 0);
                    v_isSharedCheck_614_ = (!lean_is_exclusive(v_acc_595_)) as u8;
                    if v_isSharedCheck_614_ == 0 {
                        v___x_605_ = v_acc_595_;
                        v_isShared_606_ = v_isSharedCheck_614_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_603_);
                        lean_dec(v_acc_595_);
                        v___x_605_ = lean_box(0);
                        v_isShared_606_ = v_isSharedCheck_614_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_607_ = lean_string_utf8_extract(v___x_588_, v___x_589_, v___x_590_);
                v___x_608_ = lean_string_append(v_val_603_, v___x_607_);
                lean_dec_ref(v___x_607_);
                v___x_609_ = lean_string_append(v___x_608_, v_out_600_);
                lean_dec_ref(v_out_600_);
                if v_isShared_606_ == 0 {
                    lean_ctor_set(v___x_605_, 0, v___x_609_);
                    v___x_611_ = v___x_605_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_609_);
                    v___x_611_ = v_reuseFailAlloc_613_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_612_ = lean_apply_4(
                    v_recur_597_,
                    v_it_599_,
                    v___x_611_,
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_612_;
            }
            4 => {
                v___x_619_ = lean_string_utf8_extract(
                    v_name_591_,
                    v_startInclusive_617_,
                    v_endExclusive_618_,
                );
                lean_dec(v_endExclusive_618_);
                lean_dec(v_startInclusive_617_);
                v___x_620_ = lean_unsigned_to_nat(0);
                v___x_621_ = lean_string_utf8_get(v___x_619_, v___x_620_);
                v___x_622_ = 97;
                v___x_623_ = lean_uint32_dec_le(v___x_622_, v___x_621_);
                if v___x_623_ == 0 {
                    v___x_624_ = lean_string_utf8_set(v___x_619_, v___x_620_, v___x_621_);
                    v_it_599_ = v_it_616_;
                    v_out_600_ = v___x_624_;
                    state = 1;
                    continue;
                } else {
                    v___x_625_ = 122;
                    v___x_626_ = lean_uint32_dec_le(v___x_621_, v___x_625_);
                    if v___x_626_ == 0 {
                        v___x_627_ = lean_string_utf8_set(v___x_619_, v___x_620_, v___x_621_);
                        v_it_599_ = v_it_616_;
                        v_out_600_ = v___x_627_;
                        state = 1;
                        continue;
                    } else {
                        v___x_628_ = 4294967264;
                        v___x_629_ = lean_uint32_add(v___x_621_, v___x_628_);
                        v___x_630_ = lean_string_utf8_set(v___x_619_, v___x_620_, v___x_629_);
                        v_it_599_ = v_it_616_;
                        v_out_600_ = v___x_630_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_636_ = lean_nat_dec_eq(v_searcher_632_, v___x_592_);
                if v___x_636_ == 0 {
                    lean_dec(v___x_592_);
                    v___x_637_ = lean_string_utf8_get_fast(v_name_591_, v_searcher_632_);
                    v___x_638_ = 45;
                    v___x_639_ = lean_uint32_dec_eq(v___x_637_, v___x_638_);
                    if v___x_639_ == 0 {
                        v___x_640_ = lean_string_utf8_next_fast(v_name_591_, v_searcher_632_);
                        lean_dec(v_searcher_632_);
                        if v_isShared_635_ == 0 {
                            lean_ctor_set(v___x_634_, 1, v___x_640_);
                            v___x_642_ = v___x_634_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_644_, 0, v_currPos_631_);
                            lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_640_);
                            v___x_642_ = v_reuseFailAlloc_644_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_645_ = lean_string_utf8_next_fast(v_name_591_, v_searcher_632_);
                        v___x_646_ = lean_nat_sub(v___x_645_, v_searcher_632_);
                        v___x_647_ = lean_nat_add(v_searcher_632_, v___x_646_);
                        lean_dec(v___x_646_);
                        v_slice_648_ = l_String_Slice_subslice_x21(
                            v___x_593_,
                            v_currPos_631_,
                            v_searcher_632_,
                        );
                        lean_inc(v___x_647_);
                        if v_isShared_635_ == 0 {
                            lean_ctor_set(v___x_634_, 1, v___x_647_);
                            lean_ctor_set(v___x_634_, 0, v___x_647_);
                            v_nextIt_650_ = v___x_634_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_647_);
                            lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_647_);
                            v_nextIt_650_ = v_reuseFailAlloc_653_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_634_);
                    lean_dec(v_searcher_632_);
                    v___x_654_ = lean_box(1);
                    v_it_616_ = v___x_654_;
                    v_startInclusive_617_ = v_currPos_631_;
                    v_endExclusive_618_ = v___x_592_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_643_ = lean_apply_4(
                    v_recur_597_,
                    v___x_642_,
                    v_acc_595_,
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_643_;
            }
            7 => {
                v_startInclusive_651_ = lean_ctor_get(v_slice_648_, 0);
                lean_inc(v_startInclusive_651_);
                v_endExclusive_652_ = lean_ctor_get(v_slice_648_, 1);
                lean_inc(v_endExclusive_652_);
                lean_dec_ref(v_slice_648_);
                v_it_616_ = v_nextIt_650_;
                v_startInclusive_617_ = v_startInclusive_651_;
                v_endExclusive_618_ = v_endExclusive_652_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_Name_toCanonical___lam__0___boxed(
    mut v___x_656_: *mut LeanObject,
    mut v___x_657_: *mut LeanObject,
    mut v___x_658_: *mut LeanObject,
    mut v_name_659_: *mut LeanObject,
    mut v___x_660_: *mut LeanObject,
    mut v___x_661_: *mut LeanObject,
    mut v_it_662_: *mut LeanObject,
    mut v_acc_663_: *mut LeanObject,
    mut v_hP_664_: *mut LeanObject,
    mut v_recur_665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_666_: *mut LeanObject = core::ptr::null_mut();
    v_res_666_ = l_Std_Http_Header_Name_toCanonical___lam__0(
        v___x_656_,
        v___x_657_,
        v___x_658_,
        v_name_659_,
        v___x_660_,
        v___x_661_,
        v_it_662_,
        v_acc_663_,
        v_hP_664_,
        v_recur_665_,
    );
    lean_dec_ref(v___x_661_);
    lean_dec_ref(v_name_659_);
    lean_dec(v___x_658_);
    lean_dec(v___x_657_);
    lean_dec_ref(v___x_656_);
    return v_res_666_;
}
pub unsafe fn _init_l_Std_Http_Header_Name_toCanonical___closed__2() -> *mut LeanObject {
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_669_ = l_Std_Http_Header_Name_toCanonical___closed__1;
    v___x_670_ = lean_string_utf8_byte_size(v___x_669_);
    return v___x_670_;
}
pub unsafe fn l_Std_Http_Header_Name_toCanonical(
    mut v_name_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    v___f_673_ = l_Std_Http_Header_Name_toCanonical___closed__0;
    v___x_674_ = lean_unsigned_to_nat(0);
    v___x_675_ = lean_string_utf8_byte_size(v_name_672_);
    lean_inc_ref(v_name_672_);
    v___x_676_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_676_, 0, v_name_672_);
    lean_ctor_set(v___x_676_, 1, v___x_674_);
    lean_ctor_set(v___x_676_, 2, v___x_675_);
    lean_inc_ref(v___x_676_);
    v_it_677_ = l_String_Slice_splitToSubslice___redArg(v___x_676_, v___f_673_);
    v___x_678_ = l_Std_Http_Header_Name_toCanonical___closed__1;
    v___x_679_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_toCanonical___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_toCanonical___closed__2_once),
        _init_l_Std_Http_Header_Name_toCanonical___closed__2,
    );
    v___f_680_ = lean_alloc_closure(
        l_Std_Http_Header_Name_toCanonical___lam__0___boxed as *mut core::ffi::c_void,
        10,
        6,
    );
    lean_closure_set(v___f_680_, 0, v___x_678_);
    lean_closure_set(v___f_680_, 1, v___x_674_);
    lean_closure_set(v___f_680_, 2, v___x_679_);
    lean_closure_set(v___f_680_, 3, v_name_672_);
    lean_closure_set(v___f_680_, 4, v___x_675_);
    lean_closure_set(v___f_680_, 5, v___x_676_);
    v___x_681_ = lean_box(0);
    v___x_682_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_680_, v_it_677_, v___x_681_, lean_box(0));
    if lean_obj_tag(v___x_682_) == 0 {
        let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
        v___x_683_ = l_Std_Http_Header_Name_toCanonical___closed__3;
        return v___x_683_;
    } else {
        let mut v_val_684_: *mut LeanObject = core::ptr::null_mut();
        v_val_684_ = lean_ctor_get(v___x_682_, 0);
        lean_inc(v_val_684_);
        lean_dec_ref_known(v___x_682_, 1);
        return v_val_684_;
    }
}
pub unsafe fn l_Std_Http_Header_Name_is(
    mut v_name_685_: *mut LeanObject,
    mut v_s_686_: *mut LeanObject,
) -> u8 {
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    v___x_687_ = lean_unsigned_to_nat(0);
    v___x_688_ =
        l_String_mapAux___at___00Std_Http_Header_Name_ofString_x3f_spec__0(v_s_686_, v___x_687_);
    v___x_689_ = lean_string_dec_eq(v_name_685_, v___x_688_);
    lean_dec_ref(v___x_688_);
    return v___x_689_;
}
pub unsafe fn l_Std_Http_Header_Name_is___boxed(
    mut v_name_690_: *mut LeanObject,
    mut v_s_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_692_: u8 = 0;
    let mut v_r_693_: *mut LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Std_Http_Header_Name_is(v_name_690_, v_s_691_);
    lean_dec_ref(v_name_690_);
    v_r_693_ = lean_box((v_res_692_) as usize);
    return v_r_693_;
}
pub unsafe fn l_Std_Http_Header_Name_instToString___lam__1(
    mut v_name_694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    v___f_695_ = l_Std_Http_Header_Name_toCanonical___closed__0;
    v___x_696_ = lean_unsigned_to_nat(0);
    v___x_697_ = lean_string_utf8_byte_size(v_name_694_);
    lean_inc_ref(v_name_694_);
    v___x_698_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_698_, 0, v_name_694_);
    lean_ctor_set(v___x_698_, 1, v___x_696_);
    lean_ctor_set(v___x_698_, 2, v___x_697_);
    lean_inc_ref(v___x_698_);
    v_it_699_ = l_String_Slice_splitToSubslice___redArg(v___x_698_, v___f_695_);
    v___x_700_ = l_Std_Http_Header_Name_toCanonical___closed__1;
    v___x_701_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_toCanonical___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_Header_Name_toCanonical___closed__2_once),
        _init_l_Std_Http_Header_Name_toCanonical___closed__2,
    );
    v___f_702_ = lean_alloc_closure(
        l_Std_Http_Header_Name_toCanonical___lam__0___boxed as *mut core::ffi::c_void,
        10,
        6,
    );
    lean_closure_set(v___f_702_, 0, v___x_700_);
    lean_closure_set(v___f_702_, 1, v___x_696_);
    lean_closure_set(v___f_702_, 2, v___x_701_);
    lean_closure_set(v___f_702_, 3, v_name_694_);
    lean_closure_set(v___f_702_, 4, v___x_697_);
    lean_closure_set(v___f_702_, 5, v___x_698_);
    v___x_703_ = lean_box(0);
    v___x_704_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_702_, v_it_699_, v___x_703_, lean_box(0));
    if lean_obj_tag(v___x_704_) == 0 {
        let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
        v___x_705_ = l_Std_Http_Header_Name_toCanonical___closed__3;
        return v___x_705_;
    } else {
        let mut v_val_706_: *mut LeanObject = core::ptr::null_mut();
        v_val_706_ = lean_ctor_get(v___x_704_, 0);
        lean_inc(v_val_706_);
        lean_dec_ref_known(v___x_704_, 1);
        return v_val_706_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Headers_Name(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Headers_Name(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Http_Header_Name_isValidHeaderValue___autoParam =
        _init_l_Std_Http_Header_Name_isValidHeaderValue___autoParam();
    lean_mark_persistent(l_Std_Http_Header_Name_isValidHeaderValue___autoParam);
    l_Std_Http_Header_Name_isLowerCase___autoParam =
        _init_l_Std_Http_Header_Name_isLowerCase___autoParam();
    lean_mark_persistent(l_Std_Http_Header_Name_isLowerCase___autoParam);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Headers_Name(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Iter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Headers_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Data_Headers_Name(builtin);
}
