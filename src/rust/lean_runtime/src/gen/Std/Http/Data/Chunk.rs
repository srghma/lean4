// Lean compiler output
// Module: Std.Http.Data.Chunk
// Imports: Std.Http.Internal Std.Http.Data.Headers Std.Http.Internal.String
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
    l_Array_mapFinIdxM_map___redArg,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_toDigits, l_String_quote};
use crate::r#gen::Init::Data::String::Pattern::Char::l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_splitToSubslice___redArg;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::UInt::BasicAux::l_UInt32_toUInt8___boxed;
use crate::r#gen::Init::Prelude::{
    l_ByteArray_empty, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom,
    l_String_decEq___boxed, l_String_hash___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
};
use crate::r#gen::Std::Http::Data::Headers::Name::l_Std_Http_Header_Name_ofString_x21;
use crate::r#gen::Std::Http::Data::Headers::Value::l_Std_Http_Header_Value_ofString_x21;
use crate::r#gen::Std::Http::Data::Headers::{
    initialize_Std_Http_Data_Headers, l_Std_Http_Headers_empty, l_Std_Http_Headers_fold___redArg,
    l_Std_Http_Headers_merge, l_Std_Http_Headers_toArray, l_Std_Http_Headers_toList,
    l_Std_Http_instInhabitedHeaders_default, runtime_initialize_Std_Http_Data_Headers,
};
use crate::r#gen::Std::Http::Internal::IndexMultiMap::{
    l_Std_Internal_IndexMultiMap_empty, l_Std_Internal_IndexMultiMap_instDecidableMem___redArg,
};
use crate::r#gen::Std::Http::Internal::String::{
    initialize_Std_Http_Internal_String, l_Std_Http_Internal_isToken,
    l_Std_Http_Internal_quoteHttpString___redArg, meta_initialize_Std_Http_Internal_String,
};
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_data, lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_string_validate_utf8,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::{lean_string_append, lean_string_to_utf8};
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_uint32_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_byte_array_mk, lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_dec_eq, lean_string_from_utf8_unchecked, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint32_dec_le,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_4, lean_box,
    lean_box_uint32, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value:
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
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value
) as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value:
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
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value
) as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value:
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
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value
) as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__3_value:
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
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__3_value
) as *mut LeanObject;
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_0:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_1:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_2:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__3_value
        ) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value
) as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5_value:
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
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5_value
) as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__6_value:
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
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__6_value
) as *mut LeanObject;
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_0:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_1:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value
        ) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_2:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value
        ) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__6_value
        ) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value
) as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__8_value:
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
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__8_value
) as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9_value:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__8_value
        ) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9_value
) as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10_value:
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
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10_value
) as *mut LeanObject;
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_0:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10_value) as *mut LeanObject,14249328086033210933 as *mut LeanObject] };
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value
) as *mut LeanObject;
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__14_value:
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
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__14_value
) as *mut LeanObject;
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_0:
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
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__14_value) as *mut LeanObject,3488656302031949961 as *mut LeanObject] };
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value
) as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__16_value:
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
        core::ptr::addr_of!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__16_value
) as *mut LeanObject;
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__1_value:
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
    m_data: [118, 97, 108, 117, 101, 0],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__2_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__2_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__8_value:
    LeanStringObject<2> = LeanStringObject {
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
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__10_value:
    LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        105, 115, 86, 97, 108, 105, 100, 69, 120, 116, 101, 110, 115, 105, 111, 110, 78, 97, 109,
        101, 0,
    ],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__11_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12_value:
    LeanStringObject<2> = LeanStringObject {
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
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__14_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__14_value)
        as *mut LeanObject;
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__14_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionName___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Chunk_instReprExtensionName_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instReprExtensionName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Chunk_instReprExtensionName: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instBEqExtensionName___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Chunk_instBEqExtensionName_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instBEqExtensionName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instBEqExtensionName___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Chunk_instBEqExtensionName: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instBEqExtensionName___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Chunk_instHashableExtensionName___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Http_Chunk_instHashableExtensionName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instHashableExtensionName___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Chunk_instHashableExtensionName: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instHashableExtensionName___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Chunk_instInhabitedExtensionName: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instToStringExtensionName___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Chunk_instToStringExtensionName___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instToStringExtensionName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instToStringExtensionName___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Chunk_instToStringExtensionName: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instToStringExtensionName___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 67, 104, 117, 110, 107, 0,
        ],
    };
static mut l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__1_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 67, 104, 117, 110, 107, 46, 69, 120, 116, 101,
            110, 115, 105, 111, 110, 78, 97, 109, 101, 46, 111, 102, 83, 116, 114, 105, 110, 103,
            33, 0,
        ],
    };
static mut l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__2_value: LeanStringObject<25> =
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
            105, 110, 118, 97, 108, 105, 100, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 32,
            110, 97, 109, 101, 58, 32, 0,
        ],
    };
static mut l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__2_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__0_value:
    LeanStringObject<22> = LeanStringObject {
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
        105, 115, 86, 97, 108, 105, 100, 69, 120, 116, 101, 110, 115, 105, 111, 110, 86, 97, 108,
        117, 101, 0,
    ],
};
static mut l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instReprExtensionValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Chunk_instReprExtensionValue_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instReprExtensionValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionValue___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Chunk_instReprExtensionValue: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instReprExtensionValue___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instBEqExtensionValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Chunk_instBEqExtensionValue_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instBEqExtensionValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instBEqExtensionValue___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Chunk_instBEqExtensionValue: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instBEqExtensionValue___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0_value: LeanStringObject<1> =
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
static mut l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Chunk_ExtensionValue_instInhabited: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionValue_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Chunk_ExtensionValue_instToString___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_ExtensionValue_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionValue_instToString___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Chunk_ExtensionValue_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionValue_instToString___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 67, 104, 117, 110, 107, 46, 69, 120, 116, 101,
            110, 115, 105, 111, 110, 86, 97, 108, 117, 101, 46, 111, 102, 83, 116, 114, 105, 110,
            103, 33, 0,
        ],
    };
static mut l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 32,
            118, 97, 108, 117, 101, 58, 32, 0,
        ],
    };
static mut l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_instInhabitedChunk_default___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Std_Http_instInhabitedChunk_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_instInhabitedChunk_default___closed__0_value) as *mut LeanObject;
static mut l_Std_Http_instInhabitedChunk_default___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_instInhabitedChunk_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_instInhabitedChunk_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_instInhabitedChunk: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Chunk_empty: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0_value: LeanStringObject<2> =
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
        m_data: [59, 0],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1_value: LeanStringObject<2> =
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
        m_data: [61, 0],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10_value: LeanStringObject<3> =
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
        m_data: [13, 10, 0],
    };
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10_value)
        as *mut LeanObject;
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Chunk_instEncodeV11___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_UInt32_toUInt8___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Chunk_instEncodeV11___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Chunk_instEncodeV11___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Chunk_instEncodeV11___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Chunk_instEncodeV11___closed__3_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Chunk_instEncodeV11___lam__2 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 3,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Chunk_instEncodeV11___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___closed__3_value) as *mut LeanObject;
pub static mut l_Std_Http_Chunk_instEncodeV11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Chunk_instEncodeV11___closed__3_value) as *mut LeanObject;
pub static mut l_Std_Http_instInhabitedTrailer_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_instInhabitedTrailer: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Trailer_empty: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Trailer_insert___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Std_Http_Trailer_insert___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_insert___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Trailer_erase___closed__0_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Trailer_erase___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Trailer_insert___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Chunk_instHashableExtensionName___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Http_Trailer_erase___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_erase___closed__0_value) as *mut LeanObject;
static mut l_Std_Http_Trailer_erase___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Trailer_erase___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Trailer_erase___closed__2_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_Http_Trailer_erase___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_erase___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0_value: LeanStringObject<3> =
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
        m_data: [58, 32, 0],
    };
static mut l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2_value: LeanStringObject<2> =
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
static mut l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2_value)
        as *mut LeanObject;
static mut l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [48, 13, 10, 0],
    };
static mut l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Trailer_instEncodeV11___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Trailer_instEncodeV11___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Trailer_instEncodeV11___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_instEncodeV11___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Trailer_instEncodeV11___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Trailer_instEncodeV11___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Trailer_instEncodeV11___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Trailer_instEncodeV11___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_instEncodeV11___closed__1_value) as *mut LeanObject;
pub static mut l_Std_Http_Trailer_instEncodeV11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Trailer_instEncodeV11___closed__1_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12()
-> *mut LeanObject {
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    v___x_929_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10;
    v___x_930_ = l_Lean_mkAtom(v___x_929_);
    return v___x_930_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13()
-> *mut LeanObject {
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    v___x_931_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12,
    );
    v___x_932_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5;
    v___x_933_ = lean_array_push(v___x_932_, v___x_931_);
    return v___x_933_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17()
-> *mut LeanObject {
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    v___x_944_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__16;
    v___x_945_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5;
    v___x_946_ = lean_array_push(v___x_945_, v___x_944_);
    return v___x_946_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18()
-> *mut LeanObject {
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    v___x_947_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17,
    );
    v___x_948_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15;
    v___x_949_ = lean_box(2);
    v___x_950_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_950_, 0, v___x_949_);
    lean_ctor_set(v___x_950_, 1, v___x_948_);
    lean_ctor_set(v___x_950_, 2, v___x_947_);
    return v___x_950_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19()
-> *mut LeanObject {
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    v___x_951_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18,
    );
    v___x_952_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13,
    );
    v___x_953_ = lean_array_push(v___x_952_, v___x_951_);
    return v___x_953_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20()
-> *mut LeanObject {
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    v___x_954_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19,
    );
    v___x_955_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11;
    v___x_956_ = lean_box(2);
    v___x_957_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_957_, 0, v___x_956_);
    lean_ctor_set(v___x_957_, 1, v___x_955_);
    lean_ctor_set(v___x_957_, 2, v___x_954_);
    return v___x_957_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21()
-> *mut LeanObject {
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    v___x_958_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20,
    );
    v___x_959_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5;
    v___x_960_ = lean_array_push(v___x_959_, v___x_958_);
    return v___x_960_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22()
-> *mut LeanObject {
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    v___x_961_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21,
    );
    v___x_962_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9;
    v___x_963_ = lean_box(2);
    v___x_964_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_964_, 0, v___x_963_);
    lean_ctor_set(v___x_964_, 1, v___x_962_);
    lean_ctor_set(v___x_964_, 2, v___x_961_);
    return v___x_964_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23()
-> *mut LeanObject {
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    v___x_965_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22,
    );
    v___x_966_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5;
    v___x_967_ = lean_array_push(v___x_966_, v___x_965_);
    return v___x_967_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24()
-> *mut LeanObject {
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    v___x_968_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23,
    );
    v___x_969_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7;
    v___x_970_ = lean_box(2);
    v___x_971_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_971_, 0, v___x_970_);
    lean_ctor_set(v___x_971_, 1, v___x_969_);
    lean_ctor_set(v___x_971_, 2, v___x_968_);
    return v___x_971_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25()
-> *mut LeanObject {
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    v___x_972_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24,
    );
    v___x_973_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5;
    v___x_974_ = lean_array_push(v___x_973_, v___x_972_);
    return v___x_974_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26()
-> *mut LeanObject {
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    v___x_975_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25,
    );
    v___x_976_ = l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4;
    v___x_977_ = lean_box(2);
    v___x_978_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_978_, 0, v___x_977_);
    lean_ctor_set(v___x_978_, 1, v___x_976_);
    lean_ctor_set(v___x_978_, 2, v___x_975_);
    return v___x_978_;
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam()
-> *mut LeanObject {
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    v___x_979_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26,
    );
    return v___x_979_;
}
pub unsafe fn l_Nat_cast___at___00Std_Http_Chunk_instReprExtensionName_repr_spec__0(
    mut v_a_980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_981_ = lean_nat_to_int(v_a_980_);
    return v___x_981_;
}
pub unsafe fn _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    v___x_995_ = lean_unsigned_to_nat(9);
    v___x_996_ = lean_nat_to_int(v___x_995_);
    return v___x_996_;
}
pub unsafe fn _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    v___x_1007_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0;
    v___x_1008_ = lean_string_length(v___x_1007_);
    return v___x_1008_;
}
pub unsafe fn _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16()
-> *mut LeanObject {
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1009_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15_once
        ),
        _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15,
    );
    v___x_1010_ = lean_nat_to_int(v___x_1009_);
    return v___x_1010_;
}
pub unsafe fn l_Std_Http_Chunk_instReprExtensionName_repr___redArg(
    mut v_x_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: u8 = 0;
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    v___x_1016_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5;
    v___x_1017_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6;
    v___x_1018_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7_once
        ),
        _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7,
    );
    v___x_1019_ = l_String_quote(v_x_1015_);
    v___x_1020_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1020_, 0, v___x_1019_);
    v___x_1021_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1021_, 0, v___x_1018_);
    lean_ctor_set(v___x_1021_, 1, v___x_1020_);
    v___x_1022_ = 0;
    v___x_1023_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1023_, 0, v___x_1021_);
    lean_ctor_set_uint8(
        v___x_1023_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1022_,
    );
    v___x_1024_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1024_, 0, v___x_1017_);
    lean_ctor_set(v___x_1024_, 1, v___x_1023_);
    v___x_1025_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9;
    v___x_1026_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1026_, 0, v___x_1024_);
    lean_ctor_set(v___x_1026_, 1, v___x_1025_);
    v___x_1027_ = lean_box(1);
    v___x_1028_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1028_, 0, v___x_1026_);
    lean_ctor_set(v___x_1028_, 1, v___x_1027_);
    v___x_1029_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__11;
    v___x_1030_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1030_, 0, v___x_1028_);
    lean_ctor_set(v___x_1030_, 1, v___x_1029_);
    v___x_1031_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1031_, 0, v___x_1030_);
    lean_ctor_set(v___x_1031_, 1, v___x_1016_);
    v___x_1032_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13;
    v___x_1033_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1033_, 0, v___x_1031_);
    lean_ctor_set(v___x_1033_, 1, v___x_1032_);
    v___x_1034_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16_once
        ),
        _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16,
    );
    v___x_1035_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17;
    v___x_1036_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1036_, 0, v___x_1035_);
    lean_ctor_set(v___x_1036_, 1, v___x_1033_);
    v___x_1037_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18;
    v___x_1038_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1038_, 0, v___x_1036_);
    lean_ctor_set(v___x_1038_, 1, v___x_1037_);
    v___x_1039_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1039_, 0, v___x_1034_);
    lean_ctor_set(v___x_1039_, 1, v___x_1038_);
    v___x_1040_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1040_, 0, v___x_1039_);
    lean_ctor_set_uint8(
        v___x_1040_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1022_,
    );
    return v___x_1040_;
}
pub unsafe fn l_Std_Http_Chunk_instReprExtensionName_repr(
    mut v_x_1041_: *mut LeanObject,
    mut v_prec_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1043_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg(v_x_1041_);
    return v___x_1043_;
}
pub unsafe fn l_Std_Http_Chunk_instReprExtensionName_repr___boxed(
    mut v_x_1044_: *mut LeanObject,
    mut v_prec_1045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1046_: *mut LeanObject = core::ptr::null_mut();
    v_res_1046_ = l_Std_Http_Chunk_instReprExtensionName_repr(v_x_1044_, v_prec_1045_);
    lean_dec(v_prec_1045_);
    return v_res_1046_;
}
pub unsafe fn l_Std_Http_Chunk_instDecidableEqExtensionName_decEq(
    mut v_x_1049_: *mut LeanObject,
    mut v_x_1050_: *mut LeanObject,
) -> u8 {
    let mut v___x_1051_: u8 = 0;
    v___x_1051_ = lean_string_dec_eq(v_x_1049_, v_x_1050_);
    return v___x_1051_;
}
pub unsafe fn l_Std_Http_Chunk_instDecidableEqExtensionName_decEq___boxed(
    mut v_x_1052_: *mut LeanObject,
    mut v_x_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1054_: u8 = 0;
    let mut v_r_1055_: *mut LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Std_Http_Chunk_instDecidableEqExtensionName_decEq(v_x_1052_, v_x_1053_);
    lean_dec_ref(v_x_1053_);
    lean_dec_ref(v_x_1052_);
    v_r_1055_ = lean_box((v_res_1054_) as usize);
    return v_r_1055_;
}
pub unsafe fn l_Std_Http_Chunk_instDecidableEqExtensionName(
    mut v_x_1056_: *mut LeanObject,
    mut v_x_1057_: *mut LeanObject,
) -> u8 {
    let mut v___x_1058_: u8 = 0;
    v___x_1058_ = lean_string_dec_eq(v_x_1056_, v_x_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Std_Http_Chunk_instDecidableEqExtensionName___boxed(
    mut v_x_1059_: *mut LeanObject,
    mut v_x_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1061_: u8 = 0;
    let mut v_r_1062_: *mut LeanObject = core::ptr::null_mut();
    v_res_1061_ = l_Std_Http_Chunk_instDecidableEqExtensionName(v_x_1059_, v_x_1060_);
    lean_dec_ref(v_x_1060_);
    lean_dec_ref(v_x_1059_);
    v_r_1062_ = lean_box((v_res_1061_) as usize);
    return v_r_1062_;
}
pub unsafe fn l_Std_Http_Chunk_instBEqExtensionName_beq(
    mut v_x_1063_: *mut LeanObject,
    mut v_x_1064_: *mut LeanObject,
) -> u8 {
    let mut v___x_1065_: u8 = 0;
    v___x_1065_ = lean_string_dec_eq(v_x_1063_, v_x_1064_);
    return v___x_1065_;
}
pub unsafe fn l_Std_Http_Chunk_instBEqExtensionName_beq___boxed(
    mut v_x_1066_: *mut LeanObject,
    mut v_x_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1068_: u8 = 0;
    let mut v_r_1069_: *mut LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Std_Http_Chunk_instBEqExtensionName_beq(v_x_1066_, v_x_1067_);
    lean_dec_ref(v_x_1067_);
    lean_dec_ref(v_x_1066_);
    v_r_1069_ = lean_box((v_res_1068_) as usize);
    return v_r_1069_;
}
pub unsafe fn l_Std_Http_Chunk_instToStringExtensionName___lam__0(
    mut v_name_1075_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_name_1075_);
    return v_name_1075_;
}
pub unsafe fn l_Std_Http_Chunk_instToStringExtensionName___lam__0___boxed(
    mut v_name_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1077_: *mut LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Std_Http_Chunk_instToStringExtensionName___lam__0(v_name_1076_);
    lean_dec_ref(v_name_1076_);
    return v_res_1077_;
}
pub unsafe fn l_Std_Http_Chunk_ExtensionName_ofString_x3f(
    mut v_s_1080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1081_: u8 = 0;
    lean_inc_ref(v_s_1080_);
    v___x_1081_ = l_Std_Http_Internal_isToken(v_s_1080_);
    if v___x_1081_ == 0 {
        let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_1080_);
        v___x_1082_ = lean_box(0);
        return v___x_1082_;
    } else {
        let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
        v___x_1083_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1083_, 0, v_s_1080_);
        return v___x_1083_;
    }
}
pub unsafe fn l_panic___at___00Std_Http_Chunk_ExtensionName_ofString_x21_spec__0(
    mut v_msg_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12;
    v___x_1086_ = lean_panic_fn_borrowed(v___x_1085_, v_msg_1084_);
    return v___x_1086_;
}
pub unsafe fn l_Std_Http_Chunk_ExtensionName_ofString_x21(
    mut v_s_1090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_s_1090_);
    v___x_1091_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_s_1090_);
    if lean_obj_tag(v___x_1091_) == 0 {
        let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
        v___x_1092_ = l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0;
        v___x_1093_ = l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__1;
        v___x_1094_ = lean_unsigned_to_nat(85);
        v___x_1095_ = lean_unsigned_to_nat(12);
        v___x_1096_ = l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__2;
        v___x_1097_ = l_String_quote(v_s_1090_);
        v___x_1098_ = lean_string_append(v___x_1096_, v___x_1097_);
        lean_dec_ref(v___x_1097_);
        v___x_1099_ = l_mkPanicMessageWithDecl(
            v___x_1092_,
            v___x_1093_,
            v___x_1094_,
            v___x_1095_,
            v___x_1098_,
        );
        lean_dec_ref(v___x_1098_);
        v___x_1100_ =
            l_panic___at___00Std_Http_Chunk_ExtensionName_ofString_x21_spec__0(v___x_1099_);
        return v___x_1100_;
    } else {
        let mut v_val_1101_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_1090_);
        v_val_1101_ = lean_ctor_get(v___x_1091_, 0);
        lean_inc(v_val_1101_);
        lean_dec_ref_known(v___x_1091_, 1);
        return v_val_1101_;
    }
}
pub unsafe fn _init_l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam()
-> *mut LeanObject {
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    v___x_1102_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26_once
        ),
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26,
    );
    return v___x_1102_;
}
pub unsafe fn l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(
    mut v_x_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: u8 = 0;
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5;
    v___x_1108_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6;
    v___x_1109_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7_once
        ),
        _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7,
    );
    v___x_1110_ = l_String_quote(v_x_1106_);
    v___x_1111_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1111_, 0, v___x_1110_);
    v___x_1112_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1112_, 0, v___x_1109_);
    lean_ctor_set(v___x_1112_, 1, v___x_1111_);
    v___x_1113_ = 0;
    v___x_1114_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1114_, 0, v___x_1112_);
    lean_ctor_set_uint8(
        v___x_1114_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1113_,
    );
    v___x_1115_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1115_, 0, v___x_1108_);
    lean_ctor_set(v___x_1115_, 1, v___x_1114_);
    v___x_1116_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9;
    v___x_1117_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1117_, 0, v___x_1115_);
    lean_ctor_set(v___x_1117_, 1, v___x_1116_);
    v___x_1118_ = lean_box(1);
    v___x_1119_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1119_, 0, v___x_1117_);
    lean_ctor_set(v___x_1119_, 1, v___x_1118_);
    v___x_1120_ = l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__1;
    v___x_1121_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1121_, 0, v___x_1119_);
    lean_ctor_set(v___x_1121_, 1, v___x_1120_);
    v___x_1122_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1122_, 0, v___x_1121_);
    lean_ctor_set(v___x_1122_, 1, v___x_1107_);
    v___x_1123_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13;
    v___x_1124_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1124_, 0, v___x_1122_);
    lean_ctor_set(v___x_1124_, 1, v___x_1123_);
    v___x_1125_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(
            l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16_once
        ),
        _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16,
    );
    v___x_1126_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17;
    v___x_1127_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    lean_ctor_set(v___x_1127_, 1, v___x_1124_);
    v___x_1128_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18;
    v___x_1129_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1129_, 0, v___x_1127_);
    lean_ctor_set(v___x_1129_, 1, v___x_1128_);
    v___x_1130_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1130_, 0, v___x_1125_);
    lean_ctor_set(v___x_1130_, 1, v___x_1129_);
    v___x_1131_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1131_, 0, v___x_1130_);
    lean_ctor_set_uint8(
        v___x_1131_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1113_,
    );
    return v___x_1131_;
}
pub unsafe fn l_Std_Http_Chunk_instReprExtensionValue_repr(
    mut v_x_1132_: *mut LeanObject,
    mut v_prec_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    v___x_1134_ = l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(v_x_1132_);
    return v___x_1134_;
}
pub unsafe fn l_Std_Http_Chunk_instReprExtensionValue_repr___boxed(
    mut v_x_1135_: *mut LeanObject,
    mut v_prec_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1137_: *mut LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Std_Http_Chunk_instReprExtensionValue_repr(v_x_1135_, v_prec_1136_);
    lean_dec(v_prec_1136_);
    return v_res_1137_;
}
pub unsafe fn l_Std_Http_Chunk_instDecidableEqExtensionValue_decEq(
    mut v_x_1140_: *mut LeanObject,
    mut v_x_1141_: *mut LeanObject,
) -> u8 {
    let mut v___x_1142_: u8 = 0;
    v___x_1142_ = lean_string_dec_eq(v_x_1140_, v_x_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Std_Http_Chunk_instDecidableEqExtensionValue_decEq___boxed(
    mut v_x_1143_: *mut LeanObject,
    mut v_x_1144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1145_: u8 = 0;
    let mut v_r_1146_: *mut LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_Std_Http_Chunk_instDecidableEqExtensionValue_decEq(v_x_1143_, v_x_1144_);
    lean_dec_ref(v_x_1144_);
    lean_dec_ref(v_x_1143_);
    v_r_1146_ = lean_box((v_res_1145_) as usize);
    return v_r_1146_;
}
pub unsafe fn l_Std_Http_Chunk_instDecidableEqExtensionValue(
    mut v_x_1147_: *mut LeanObject,
    mut v_x_1148_: *mut LeanObject,
) -> u8 {
    let mut v___x_1149_: u8 = 0;
    v___x_1149_ = lean_string_dec_eq(v_x_1147_, v_x_1148_);
    return v___x_1149_;
}
pub unsafe fn l_Std_Http_Chunk_instDecidableEqExtensionValue___boxed(
    mut v_x_1150_: *mut LeanObject,
    mut v_x_1151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1152_: u8 = 0;
    let mut v_r_1153_: *mut LeanObject = core::ptr::null_mut();
    v_res_1152_ = l_Std_Http_Chunk_instDecidableEqExtensionValue(v_x_1150_, v_x_1151_);
    lean_dec_ref(v_x_1151_);
    lean_dec_ref(v_x_1150_);
    v_r_1153_ = lean_box((v_res_1152_) as usize);
    return v_r_1153_;
}
pub unsafe fn l_Std_Http_Chunk_instBEqExtensionValue_beq(
    mut v_x_1154_: *mut LeanObject,
    mut v_x_1155_: *mut LeanObject,
) -> u8 {
    let mut v___x_1156_: u8 = 0;
    v___x_1156_ = lean_string_dec_eq(v_x_1154_, v_x_1155_);
    return v___x_1156_;
}
pub unsafe fn l_Std_Http_Chunk_instBEqExtensionValue_beq___boxed(
    mut v_x_1157_: *mut LeanObject,
    mut v_x_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1159_: u8 = 0;
    let mut v_r_1160_: *mut LeanObject = core::ptr::null_mut();
    v_res_1159_ = l_Std_Http_Chunk_instBEqExtensionValue_beq(v_x_1157_, v_x_1158_);
    lean_dec_ref(v_x_1158_);
    lean_dec_ref(v_x_1157_);
    v_r_1160_ = lean_box((v_res_1159_) as usize);
    return v_r_1160_;
}
pub unsafe fn l_Std_Http_Chunk_ExtensionValue_instToString___lam__0(
    mut v_v_1165_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_v_1165_);
    return v_v_1165_;
}
pub unsafe fn l_Std_Http_Chunk_ExtensionValue_instToString___lam__0___boxed(
    mut v_v_1166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1167_: *mut LeanObject = core::ptr::null_mut();
    v_res_1167_ = l_Std_Http_Chunk_ExtensionValue_instToString___lam__0(v_v_1166_);
    lean_dec_ref(v_v_1166_);
    return v_res_1167_;
}
pub unsafe fn l_Std_Http_Chunk_ExtensionValue_quote(
    mut v_s_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    v___x_1171_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_1170_);
    return v___x_1171_;
}
pub unsafe fn l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0(
    mut v_x_1172_: *mut LeanObject,
) -> u8 {
    let mut v___x_1173_: u8 = 0;
    let mut v_head_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: u32 = 0;
    let mut v___x_1178_: u32 = 0;
    let mut v___x_1179_: u8 = 0;
    let mut v___x_1180_: u32 = 0;
    let mut v___x_1181_: u32 = 0;
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: u32 = 0;
    let mut v___x_1184_: u32 = 0;
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: u32 = 0;
    let mut v___x_1187_: u32 = 0;
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1193_: u32 = 0;
    let mut v___x_1194_: u32 = 0;
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: u32 = 0;
    let mut v___x_1197_: u32 = 0;
    let mut v___x_1198_: u8 = 0;
    let mut v___x_1200_: u32 = 0;
    let mut v___x_1201_: u32 = 0;
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1203_: u32 = 0;
    let mut v___x_1204_: u32 = 0;
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: u32 = 0;
    let mut v___x_1207_: u32 = 0;
    let mut v___x_1208_: u8 = 0;
    let mut v___x_1209_: u32 = 0;
    let mut v___x_1210_: u32 = 0;
    let mut v___x_1211_: u8 = 0;
    let mut v___x_1212_: u32 = 0;
    let mut v___x_1213_: u32 = 0;
    let mut v___x_1214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1172_) == 0 {
                    v___x_1173_ = 1;
                    return v___x_1173_;
                } else {
                    v_head_1174_ = lean_ctor_get(v_x_1172_, 0);
                    v_tail_1175_ = lean_ctor_get(v_x_1172_, 1);
                    v___x_1200_ = 9;
                    v___x_1201_ = lean_unbox_uint32(v_head_1174_);
                    v___x_1202_ = lean_uint32_dec_eq(v___x_1201_, v___x_1200_);
                    if v___x_1202_ == 0 {
                        v___x_1203_ = 32;
                        v___x_1204_ = lean_unbox_uint32(v_head_1174_);
                        v___x_1205_ = lean_uint32_dec_eq(v___x_1204_, v___x_1203_);
                        if v___x_1205_ == 0 {
                            v___x_1206_ = 33;
                            v___x_1207_ = lean_unbox_uint32(v_head_1174_);
                            v___x_1208_ = lean_uint32_dec_eq(v___x_1207_, v___x_1206_);
                            if v___x_1208_ == 0 {
                                v___x_1209_ = 35;
                                v___x_1210_ = lean_unbox_uint32(v_head_1174_);
                                v___x_1211_ = lean_uint32_dec_le(v___x_1209_, v___x_1210_);
                                if v___x_1211_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1212_ = 91;
                                    v___x_1213_ = lean_unbox_uint32(v_head_1174_);
                                    v___x_1214_ = lean_uint32_dec_le(v___x_1213_, v___x_1212_);
                                    if v___x_1214_ == 0 {
                                        state = 2;
                                        continue;
                                    } else {
                                        v_x_1172_ = v_tail_1175_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            } else {
                                v_x_1172_ = v_tail_1175_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v_x_1172_ = v_tail_1175_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_x_1172_ = v_tail_1175_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1177_ = 9;
                v___x_1178_ = lean_unbox_uint32(v_head_1174_);
                v___x_1179_ = lean_uint32_dec_eq(v___x_1178_, v___x_1177_);
                if v___x_1179_ == 0 {
                    v___x_1180_ = 32;
                    v___x_1181_ = lean_unbox_uint32(v_head_1174_);
                    v___x_1182_ = lean_uint32_dec_eq(v___x_1181_, v___x_1180_);
                    if v___x_1182_ == 0 {
                        v___x_1183_ = 33;
                        v___x_1184_ = lean_unbox_uint32(v_head_1174_);
                        v___x_1185_ = lean_uint32_dec_le(v___x_1183_, v___x_1184_);
                        if v___x_1185_ == 0 {
                            return v___x_1185_;
                        } else {
                            v___x_1186_ = 126;
                            v___x_1187_ = lean_unbox_uint32(v_head_1174_);
                            v___x_1188_ = lean_uint32_dec_le(v___x_1187_, v___x_1186_);
                            if v___x_1188_ == 0 {
                                return v___x_1188_;
                            } else {
                                v_x_1172_ = v_tail_1175_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        v_x_1172_ = v_tail_1175_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_x_1172_ = v_tail_1175_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_1193_ = 93;
                v___x_1194_ = lean_unbox_uint32(v_head_1174_);
                v___x_1195_ = lean_uint32_dec_le(v___x_1193_, v___x_1194_);
                if v___x_1195_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1196_ = 126;
                    v___x_1197_ = lean_unbox_uint32(v_head_1174_);
                    v___x_1198_ = lean_uint32_dec_le(v___x_1197_, v___x_1196_);
                    if v___x_1198_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_x_1172_ = v_tail_1175_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0___boxed(
    mut v_x_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1220_: u8 = 0;
    let mut v_r_1221_: *mut LeanObject = core::ptr::null_mut();
    v_res_1220_ = l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0(v_x_1219_);
    lean_dec(v_x_1219_);
    v_r_1221_ = lean_box((v_res_1220_) as usize);
    return v_r_1221_;
}
pub unsafe fn l_Std_Http_Chunk_ExtensionValue_ofString_x3f(
    mut v_s_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: u8 = 0;
    lean_inc_ref(v_s_1222_);
    v___x_1223_ = lean_string_data(v_s_1222_);
    v___x_1224_ =
        l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0(v___x_1223_);
    lean_dec(v___x_1223_);
    if v___x_1224_ == 0 {
        let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_1222_);
        v___x_1225_ = lean_box(0);
        return v___x_1225_;
    } else {
        let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
        v___x_1226_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1226_, 0, v_s_1222_);
        return v___x_1226_;
    }
}
pub unsafe fn l_panic___at___00Std_Http_Chunk_ExtensionValue_ofString_x21_spec__0(
    mut v_msg_1227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    v___x_1228_ = l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0;
    v___x_1229_ = lean_panic_fn_borrowed(v___x_1228_, v_msg_1227_);
    return v___x_1229_;
}
pub unsafe fn l_Std_Http_Chunk_ExtensionValue_ofString_x21(
    mut v_s_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_s_1232_);
    v___x_1233_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_s_1232_);
    if lean_obj_tag(v___x_1233_) == 0 {
        let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
        v___x_1234_ = l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0;
        v___x_1235_ = l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0;
        v___x_1236_ = lean_unsigned_to_nat(152);
        v___x_1237_ = lean_unsigned_to_nat(12);
        v___x_1238_ = l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1;
        v___x_1239_ = l_String_quote(v_s_1232_);
        v___x_1240_ = lean_string_append(v___x_1238_, v___x_1239_);
        lean_dec_ref(v___x_1239_);
        v___x_1241_ = l_mkPanicMessageWithDecl(
            v___x_1234_,
            v___x_1235_,
            v___x_1236_,
            v___x_1237_,
            v___x_1240_,
        );
        lean_dec_ref(v___x_1240_);
        v___x_1242_ =
            l_panic___at___00Std_Http_Chunk_ExtensionValue_ofString_x21_spec__0(v___x_1241_);
        return v___x_1242_;
    } else {
        let mut v_val_1243_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_1232_);
        v_val_1243_ = lean_ctor_get(v___x_1233_, 0);
        lean_inc(v_val_1243_);
        lean_dec_ref_known(v___x_1233_, 1);
        return v_val_1243_;
    }
}
pub unsafe fn _init_l_Std_Http_instInhabitedChunk_default___closed__1() -> *mut LeanObject {
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Std_Http_instInhabitedChunk_default___closed__0;
    v___x_1247_ = l_ByteArray_empty;
    v___x_1248_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1248_, 0, v___x_1247_);
    lean_ctor_set(v___x_1248_, 1, v___x_1246_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedChunk_default() -> *mut LeanObject {
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    v___x_1249_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedChunk_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedChunk_default___closed__1_once),
        _init_l_Std_Http_instInhabitedChunk_default___closed__1,
    );
    return v___x_1249_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedChunk() -> *mut LeanObject {
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    v___x_1250_ = l_Std_Http_instInhabitedChunk_default;
    return v___x_1250_;
}
pub unsafe fn _init_l_Std_Http_Chunk_empty() -> *mut LeanObject {
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    v___x_1251_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedChunk_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedChunk_default___closed__1_once),
        _init_l_Std_Http_instInhabitedChunk_default___closed__1,
    );
    return v___x_1251_;
}
pub unsafe fn l_Std_Http_Chunk_ofByteArray(mut v_data_1252_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    v___x_1253_ = l_Std_Http_instInhabitedChunk_default___closed__0;
    v___x_1254_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1254_, 0, v_data_1252_);
    lean_ctor_set(v___x_1254_, 1, v___x_1253_);
    return v___x_1254_;
}
pub unsafe fn l_Std_Http_Chunk_insertExtension(
    mut v_chunk_1255_: *mut LeanObject,
    mut v_key_1256_: *mut LeanObject,
    mut v_value_1257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1262_: u8 = 0;
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_1258_ = lean_ctor_get(v_chunk_1255_, 0);
                v_extensions_1259_ = lean_ctor_get(v_chunk_1255_, 1);
                v_isSharedCheck_1269_ = (!lean_is_exclusive(v_chunk_1255_)) as u8;
                if v_isSharedCheck_1269_ == 0 {
                    v___x_1261_ = v_chunk_1255_;
                    v_isShared_1262_ = v_isSharedCheck_1269_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_extensions_1259_);
                    lean_inc(v_data_1258_);
                    lean_dec(v_chunk_1255_);
                    v___x_1261_ = lean_box(0);
                    v_isShared_1262_ = v_isSharedCheck_1269_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1263_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1263_, 0, v_value_1257_);
                v___x_1264_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1264_, 0, v_key_1256_);
                lean_ctor_set(v___x_1264_, 1, v___x_1263_);
                v___x_1265_ = lean_array_push(v_extensions_1259_, v___x_1264_);
                if v_isShared_1262_ == 0 {
                    lean_ctor_set(v___x_1261_, 1, v___x_1265_);
                    v___x_1267_ = v___x_1261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_data_1258_);
                    lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1265_);
                    v___x_1267_ = v_reuseFailAlloc_1268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Chunk_toString_x3f(mut v_chunk_1270_: *mut LeanObject) -> *mut LeanObject {
    let mut v_data_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: u8 = 0;
    v_data_1271_ = lean_ctor_get(v_chunk_1270_, 0);
    lean_inc_ref(v_data_1271_);
    lean_dec_ref(v_chunk_1270_);
    v___x_1272_ = lean_string_validate_utf8(v_data_1271_);
    if v___x_1272_ == 0 {
        let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_data_1271_);
        v___x_1273_ = lean_box(0);
        return v___x_1273_;
    } else {
        let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
        v___x_1274_ = lean_string_from_utf8_unchecked(v_data_1271_);
        v___x_1275_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1275_, 0, v___x_1274_);
        return v___x_1275_;
    }
}
pub unsafe fn l_Std_Http_Chunk_instEncodeV11___lam__0(
    mut v_x1_1276_: *mut LeanObject,
    mut v_x2_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    v___x_1278_ = lean_byte_array_size(v_x2_1277_);
    v___x_1279_ = lean_nat_add(v_x1_1276_, v___x_1278_);
    return v___x_1279_;
}
pub unsafe fn l_Std_Http_Chunk_instEncodeV11___lam__0___boxed(
    mut v_x1_1280_: *mut LeanObject,
    mut v_x2_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1282_: *mut LeanObject = core::ptr::null_mut();
    v_res_1282_ = l_Std_Http_Chunk_instEncodeV11___lam__0(v_x1_1280_, v_x2_1281_);
    lean_dec_ref(v_x2_1281_);
    lean_dec(v_x1_1280_);
    return v_res_1282_;
}
pub unsafe fn l_Std_Http_Chunk_instEncodeV11___lam__1(
    mut v_x1_1285_: *mut LeanObject,
    mut v_x2_1286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1287_ = lean_ctor_get(v_x2_1286_, 0);
    lean_inc(v_fst_1287_);
    v_snd_1288_ = lean_ctor_get(v_x2_1286_, 1);
    lean_inc(v_snd_1288_);
    lean_dec_ref(v_x2_1286_);
    v___x_1289_ = l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0;
    v___x_1290_ = lean_string_append(v_x1_1285_, v___x_1289_);
    v___x_1291_ = lean_string_append(v___x_1290_, v_fst_1287_);
    lean_dec(v_fst_1287_);
    if lean_obj_tag(v_snd_1288_) == 0 {
        return v___x_1291_;
    } else {
        let mut v_val_1292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
        v_val_1292_ = lean_ctor_get(v_snd_1288_, 0);
        lean_inc(v_val_1292_);
        lean_dec_ref_known(v_snd_1288_, 1);
        v___x_1293_ = l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1;
        v___x_1294_ = l_Std_Http_Internal_quoteHttpString___redArg(v_val_1292_);
        v___x_1295_ = lean_string_append(v___x_1293_, v___x_1294_);
        lean_dec_ref(v___x_1294_);
        v___x_1296_ = lean_string_append(v___x_1291_, v___x_1295_);
        lean_dec_ref(v___x_1295_);
        return v___x_1296_;
    }
}
pub unsafe fn _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11() -> *mut LeanObject {
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    v___x_1317_ = l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10;
    v___x_1318_ = lean_string_to_utf8(v___x_1317_);
    return v___x_1318_;
}
pub unsafe fn l_Std_Http_Chunk_instEncodeV11___lam__2(
    mut v___f_1319_: *mut LeanObject,
    mut v___f_1320_: *mut LeanObject,
    mut v___f_1321_: *mut LeanObject,
    mut v_buffer_1322_: *mut LeanObject,
    mut v_chunk_1323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1338_: u8 = 0;
    let mut v_data_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v_chunkLen_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1351_: usize = 0;
    let mut v___x_1352_: usize = 0;
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1354_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1366_: u8 = 0;
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: usize = 0;
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: usize = 0;
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1389_: u8 = 0;
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: usize = 0;
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: usize = 0;
    let mut v___x_1394_: usize = 0;
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_1339_ = lean_ctor_get(v_chunk_1323_, 0);
                v_extensions_1340_ = lean_ctor_get(v_chunk_1323_, 1);
                v_isSharedCheck_1396_ = (!lean_is_exclusive(v_chunk_1323_)) as u8;
                if v_isSharedCheck_1396_ == 0 {
                    v___x_1342_ = v_chunk_1323_;
                    v_isShared_1343_ = v_isSharedCheck_1396_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_extensions_1340_);
                    lean_inc(v_data_1339_);
                    lean_dec(v_chunk_1323_);
                    v___x_1342_ = lean_box(0);
                    v_isShared_1343_ = v_isSharedCheck_1396_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v_data_1326_ = lean_ctor_get(v_buffer_1322_, 0);
                lean_inc_ref(v_data_1326_);
                v_size_1327_ = lean_ctor_get(v_buffer_1322_, 1);
                lean_inc(v_size_1327_);
                lean_dec_ref(v_buffer_1322_);
                v_data_1328_ = lean_ctor_get(v___y_1325_, 0);
                v_size_1329_ = lean_ctor_get(v___y_1325_, 1);
                v_isSharedCheck_1338_ = (!lean_is_exclusive(v___y_1325_)) as u8;
                if v_isSharedCheck_1338_ == 0 {
                    v___x_1331_ = v___y_1325_;
                    v_isShared_1332_ = v_isSharedCheck_1338_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_size_1329_);
                    lean_inc(v_data_1328_);
                    lean_dec(v___y_1325_);
                    v___x_1331_ = lean_box(0);
                    v_isShared_1332_ = v_isSharedCheck_1338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1333_ = l_Array_append___redArg(v_data_1326_, v_data_1328_);
                lean_dec_ref(v_data_1328_);
                v___x_1334_ = lean_nat_add(v_size_1327_, v_size_1329_);
                lean_dec(v_size_1329_);
                lean_dec(v_size_1327_);
                if v_isShared_1332_ == 0 {
                    lean_ctor_set(v___x_1331_, 1, v___x_1334_);
                    lean_ctor_set(v___x_1331_, 0, v___x_1333_);
                    v___x_1336_ = v___x_1331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1333_);
                    lean_ctor_set(v_reuseFailAlloc_1337_, 1, v___x_1334_);
                    v___x_1336_ = v_reuseFailAlloc_1337_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1336_;
            }
            4 => {
                v_chunkLen_1344_ = lean_byte_array_size(v_data_1339_);
                v___x_1384_ = l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0;
                v___x_1385_ = lean_unsigned_to_nat(0);
                v___x_1386_ = lean_array_get_size(v_extensions_1340_);
                v___x_1387_ = l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9;
                v___x_1388_ = lean_nat_dec_lt(v___x_1385_, v___x_1386_);
                if v___x_1388_ == 0 {
                    lean_dec_ref(v_extensions_1340_);
                    lean_dec_ref(v___f_1321_);
                    v___y_1346_ = v___x_1384_;
                    state = 5;
                    continue;
                } else {
                    v___x_1389_ = lean_nat_dec_le(v___x_1386_, v___x_1386_);
                    if v___x_1389_ == 0 {
                        if v___x_1388_ == 0 {
                            lean_dec_ref(v_extensions_1340_);
                            lean_dec_ref(v___f_1321_);
                            v___y_1346_ = v___x_1384_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1390_ = 0usize;
                            v___x_1391_ = lean_usize_of_nat(v___x_1386_);
                            v___x_1392_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_1387_,
                                    v___f_1321_,
                                    v_extensions_1340_,
                                    v___x_1390_,
                                    v___x_1391_,
                                    v___x_1384_,
                                );
                            v___y_1346_ = v___x_1392_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_1393_ = 0usize;
                        v___x_1394_ = lean_usize_of_nat(v___x_1386_);
                        v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_1387_,
                            v___f_1321_,
                            v_extensions_1340_,
                            v___x_1393_,
                            v___x_1394_,
                            v___x_1384_,
                        );
                        v___y_1346_ = v___x_1395_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1347_ = lean_unsigned_to_nat(16);
                v___x_1348_ = l_Nat_toDigits(v___x_1347_, v_chunkLen_1344_);
                v___x_1349_ = lean_array_mk(v___x_1348_);
                v___x_1350_ = l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9;
                v_sz_1351_ = lean_array_size(v___x_1349_);
                v___x_1352_ = 0usize;
                v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_1350_,
                    v___f_1319_,
                    v_sz_1351_,
                    v___x_1352_,
                    v___x_1349_,
                );
                v_size_1354_ = lean_byte_array_mk(v___x_1353_);
                v___x_1355_ = lean_string_to_utf8(v___y_1346_);
                lean_dec_ref(v___y_1346_);
                v___x_1356_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once
                    ),
                    _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11,
                );
                v___x_1357_ = lean_unsigned_to_nat(5);
                v___x_1358_ = lean_mk_empty_array_with_capacity(v___x_1357_);
                v___x_1359_ = lean_array_push(v___x_1358_, v_size_1354_);
                v___x_1360_ = lean_array_push(v___x_1359_, v___x_1355_);
                v___x_1361_ = lean_array_push(v___x_1360_, v___x_1356_);
                v___x_1362_ = lean_array_push(v___x_1361_, v_data_1339_);
                v___x_1363_ = lean_array_push(v___x_1362_, v___x_1356_);
                v___x_1364_ = lean_unsigned_to_nat(0);
                v___x_1365_ = lean_array_get_size(v___x_1363_);
                v___x_1366_ = lean_nat_dec_lt(v___x_1364_, v___x_1365_);
                if v___x_1366_ == 0 {
                    lean_dec_ref(v___f_1320_);
                    if v_isShared_1343_ == 0 {
                        lean_ctor_set(v___x_1342_, 1, v___x_1364_);
                        lean_ctor_set(v___x_1342_, 0, v___x_1363_);
                        v___x_1368_ = v___x_1342_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1363_);
                        lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1364_);
                        v___x_1368_ = v_reuseFailAlloc_1369_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_1370_ = lean_nat_dec_le(v___x_1365_, v___x_1365_);
                    if v___x_1370_ == 0 {
                        if v___x_1366_ == 0 {
                            lean_dec_ref(v___f_1320_);
                            if v_isShared_1343_ == 0 {
                                lean_ctor_set(v___x_1342_, 1, v___x_1364_);
                                lean_ctor_set(v___x_1342_, 0, v___x_1363_);
                                v___x_1372_ = v___x_1342_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1363_);
                                lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1364_);
                                v___x_1372_ = v_reuseFailAlloc_1373_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v___x_1374_ = lean_usize_of_nat(v___x_1365_);
                            lean_inc_ref(v___x_1363_);
                            v___x_1375_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_1350_,
                                    v___f_1320_,
                                    v___x_1363_,
                                    v___x_1352_,
                                    v___x_1374_,
                                    v___x_1364_,
                                );
                            if v_isShared_1343_ == 0 {
                                lean_ctor_set(v___x_1342_, 1, v___x_1375_);
                                lean_ctor_set(v___x_1342_, 0, v___x_1363_);
                                v___x_1377_ = v___x_1342_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1363_);
                                lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1375_);
                                v___x_1377_ = v_reuseFailAlloc_1378_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        v___x_1379_ = lean_usize_of_nat(v___x_1365_);
                        lean_inc_ref(v___x_1363_);
                        v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_1350_,
                            v___f_1320_,
                            v___x_1363_,
                            v___x_1352_,
                            v___x_1379_,
                            v___x_1364_,
                        );
                        if v_isShared_1343_ == 0 {
                            lean_ctor_set(v___x_1342_, 1, v___x_1380_);
                            lean_ctor_set(v___x_1342_, 0, v___x_1363_);
                            v___x_1382_ = v___x_1342_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1363_);
                            lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1380_);
                            v___x_1382_ = v_reuseFailAlloc_1383_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___y_1325_ = v___x_1368_;
                state = 1;
                continue;
            }
            7 => {
                v___y_1325_ = v___x_1372_;
                state = 1;
                continue;
            }
            8 => {
                v___y_1325_ = v___x_1377_;
                state = 1;
                continue;
            }
            9 => {
                v___y_1325_ = v___x_1382_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Http_instInhabitedTrailer_default() -> *mut LeanObject {
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    v___x_1405_ = l_Std_Http_instInhabitedHeaders_default;
    return v___x_1405_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedTrailer() -> *mut LeanObject {
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    v___x_1406_ = l_Std_Http_instInhabitedHeaders_default;
    return v___x_1406_;
}
pub unsafe fn _init_l_Std_Http_Trailer_empty() -> *mut LeanObject {
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Std_Http_Headers_empty;
    return v___x_1407_;
}
pub unsafe fn l_Std_Http_Trailer_insert___lam__0(
    mut v_i_1408_: *mut LeanObject,
    mut v_x_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1409_) == 0 {
                    v___x_1410_ = lean_unsigned_to_nat(1);
                    v___x_1411_ = lean_mk_empty_array_with_capacity(v___x_1410_);
                    v___x_1412_ = lean_array_push(v___x_1411_, v_i_1408_);
                    v___x_1413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1413_, 0, v___x_1412_);
                    return v___x_1413_;
                } else {
                    v_val_1414_ = lean_ctor_get(v_x_1409_, 0);
                    v_isSharedCheck_1422_ = (!lean_is_exclusive(v_x_1409_)) as u8;
                    if v_isSharedCheck_1422_ == 0 {
                        v___x_1416_ = v_x_1409_;
                        v_isShared_1417_ = v_isSharedCheck_1422_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1414_);
                        lean_dec(v_x_1409_);
                        v___x_1416_ = lean_box(0);
                        v_isShared_1417_ = v_isSharedCheck_1422_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1418_ = lean_array_push(v_val_1414_, v_i_1408_);
                if v_isShared_1417_ == 0 {
                    lean_ctor_set(v___x_1416_, 0, v___x_1418_);
                    v___x_1420_ = v___x_1416_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
                    v___x_1420_ = v_reuseFailAlloc_1421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Trailer_insert(
    mut v_trailer_1424_: *mut LeanObject,
    mut v_name_1425_: *mut LeanObject,
    mut v_value_1426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_entries_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indexes_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1431_: u8 = 0;
    let mut v___f_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indexes_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entries_1427_ = lean_ctor_get(v_trailer_1424_, 0);
                v_indexes_1428_ = lean_ctor_get(v_trailer_1424_, 1);
                v_isSharedCheck_1442_ = (!lean_is_exclusive(v_trailer_1424_)) as u8;
                if v_isSharedCheck_1442_ == 0 {
                    v___x_1430_ = v_trailer_1424_;
                    v_isShared_1431_ = v_isSharedCheck_1442_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_indexes_1428_);
                    lean_inc(v_entries_1427_);
                    lean_dec(v_trailer_1424_);
                    v___x_1430_ = lean_box(0);
                    v_isShared_1431_ = v_isSharedCheck_1442_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1432_ = l_Std_Http_Trailer_insert___closed__0;
                v___f_1433_ = l_Std_Http_Chunk_instHashableExtensionName___closed__0;
                v_i_1434_ = lean_array_get_size(v_entries_1427_);
                v_f_1435_ = lean_alloc_closure(
                    l_Std_Http_Trailer_insert___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v_f_1435_, 0, v_i_1434_);
                lean_inc_ref(v_name_1425_);
                v___x_1436_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1436_, 0, v_name_1425_);
                lean_ctor_set(v___x_1436_, 1, v_value_1426_);
                v_entries_1437_ = lean_array_push(v_entries_1427_, v___x_1436_);
                v_indexes_1438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_1432_,
                    v___f_1433_,
                    v_indexes_1428_,
                    v_name_1425_,
                    v_f_1435_,
                );
                if v_isShared_1431_ == 0 {
                    lean_ctor_set(v___x_1430_, 1, v_indexes_1438_);
                    lean_ctor_set(v___x_1430_, 0, v_entries_1437_);
                    v___x_1440_ = v___x_1430_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_entries_1437_);
                    lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_indexes_1438_);
                    v___x_1440_ = v_reuseFailAlloc_1441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Trailer_insert_x21(
    mut v_trailer_1443_: *mut LeanObject,
    mut v_name_1444_: *mut LeanObject,
    mut v_value_1445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_entries_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indexes_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indexes_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entries_1446_ = lean_ctor_get(v_trailer_1443_, 0);
                v_indexes_1447_ = lean_ctor_get(v_trailer_1443_, 1);
                v_isSharedCheck_1463_ = (!lean_is_exclusive(v_trailer_1443_)) as u8;
                if v_isSharedCheck_1463_ == 0 {
                    v___x_1449_ = v_trailer_1443_;
                    v_isShared_1450_ = v_isSharedCheck_1463_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_indexes_1447_);
                    lean_inc(v_entries_1446_);
                    lean_dec(v_trailer_1443_);
                    v___x_1449_ = lean_box(0);
                    v_isShared_1450_ = v_isSharedCheck_1463_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1451_ = l_Std_Http_Header_Name_ofString_x21(v_name_1444_);
                v___x_1452_ = l_Std_Http_Header_Value_ofString_x21(v_value_1445_);
                v___f_1453_ = l_Std_Http_Trailer_insert___closed__0;
                v___f_1454_ = l_Std_Http_Chunk_instHashableExtensionName___closed__0;
                v_i_1455_ = lean_array_get_size(v_entries_1446_);
                v_f_1456_ = lean_alloc_closure(
                    l_Std_Http_Trailer_insert___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v_f_1456_, 0, v_i_1455_);
                lean_inc_ref(v___x_1451_);
                v___x_1457_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1457_, 0, v___x_1451_);
                lean_ctor_set(v___x_1457_, 1, v___x_1452_);
                v_entries_1458_ = lean_array_push(v_entries_1446_, v___x_1457_);
                v_indexes_1459_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_1453_,
                    v___f_1454_,
                    v_indexes_1447_,
                    v___x_1451_,
                    v_f_1456_,
                );
                if v_isShared_1450_ == 0 {
                    lean_ctor_set(v___x_1449_, 1, v_indexes_1459_);
                    lean_ctor_set(v___x_1449_, 0, v_entries_1458_);
                    v___x_1461_ = v___x_1449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_entries_1458_);
                    lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_indexes_1459_);
                    v___x_1461_ = v_reuseFailAlloc_1462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Trailer_get_x3f(
    mut v_trailer_1464_: *mut LeanObject,
    mut v_name_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: u8 = 0;
    v___f_1466_ = l_Std_Http_Trailer_insert___closed__0;
    v___f_1467_ = l_Std_Http_Chunk_instHashableExtensionName___closed__0;
    lean_inc_ref(v_name_1465_);
    v___x_1468_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_1466_,
        v___f_1467_,
        v_name_1465_,
        v_trailer_1464_,
    );
    if v___x_1468_ == 0 {
        let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_name_1465_);
        v___x_1469_ = lean_box(0);
        return v___x_1469_;
    } else {
        let mut v_entries_1470_: *mut LeanObject = core::ptr::null_mut();
        let mut v_indexes_1471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
        let mut v_entry_1474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
        v_entries_1470_ = lean_ctor_get(v_trailer_1464_, 0);
        v_indexes_1471_ = lean_ctor_get(v_trailer_1464_, 1);
        v___x_1472_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v___f_1466_,
            v___f_1467_,
            v_indexes_1471_,
            v_name_1465_,
        );
        v___x_1473_ = lean_unsigned_to_nat(0);
        v_entry_1474_ = lean_array_fget(v___x_1472_, v___x_1473_);
        lean_dec(v___x_1472_);
        v___x_1475_ = lean_array_fget_borrowed(v_entries_1470_, v_entry_1474_);
        lean_dec(v_entry_1474_);
        v_snd_1476_ = lean_ctor_get(v___x_1475_, 1);
        lean_inc(v_snd_1476_);
        v___x_1477_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1477_, 0, v_snd_1476_);
        return v___x_1477_;
    }
}
pub unsafe fn l_Std_Http_Trailer_get_x3f___boxed(
    mut v_trailer_1478_: *mut LeanObject,
    mut v_name_1479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1480_: *mut LeanObject = core::ptr::null_mut();
    v_res_1480_ = l_Std_Http_Trailer_get_x3f(v_trailer_1478_, v_name_1479_);
    lean_dec_ref(v_trailer_1478_);
    return v_res_1480_;
}
pub unsafe fn l_Std_Http_Trailer_getAll_x3f___lam__0(
    mut v___x_1481_: *mut LeanObject,
    mut v_entries_1482_: *mut LeanObject,
    mut v_x1_1483_: *mut LeanObject,
    mut v_x2_1484_: *mut LeanObject,
    mut v_x3_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1488_: *mut LeanObject = core::ptr::null_mut();
    v___x_1486_ = lean_array_fget_borrowed(v___x_1481_, v_x1_1483_);
    v___x_1487_ = lean_array_fget_borrowed(v_entries_1482_, v___x_1486_);
    v_snd_1488_ = lean_ctor_get(v___x_1487_, 1);
    lean_inc(v_snd_1488_);
    return v_snd_1488_;
}
pub unsafe fn l_Std_Http_Trailer_getAll_x3f___lam__0___boxed(
    mut v___x_1489_: *mut LeanObject,
    mut v_entries_1490_: *mut LeanObject,
    mut v_x1_1491_: *mut LeanObject,
    mut v_x2_1492_: *mut LeanObject,
    mut v_x3_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1494_: *mut LeanObject = core::ptr::null_mut();
    v_res_1494_ = l_Std_Http_Trailer_getAll_x3f___lam__0(
        v___x_1489_,
        v_entries_1490_,
        v_x1_1491_,
        v_x2_1492_,
        v_x3_1493_,
    );
    lean_dec(v_x2_1492_);
    lean_dec(v_x1_1491_);
    lean_dec_ref(v_entries_1490_);
    lean_dec_ref(v___x_1489_);
    return v_res_1494_;
}
pub unsafe fn l_Std_Http_Trailer_getAll_x3f(
    mut v_trailer_1495_: *mut LeanObject,
    mut v_name_1496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    v___f_1497_ = l_Std_Http_Trailer_insert___closed__0;
    v___f_1498_ = l_Std_Http_Chunk_instHashableExtensionName___closed__0;
    lean_inc_ref(v_name_1496_);
    v___x_1499_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_1497_,
        v___f_1498_,
        v_name_1496_,
        v_trailer_1495_,
    );
    if v___x_1499_ == 0 {
        let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_name_1496_);
        lean_dec_ref(v_trailer_1495_);
        v___x_1500_ = lean_box(0);
        return v___x_1500_;
    } else {
        let mut v_entries_1501_: *mut LeanObject = core::ptr::null_mut();
        let mut v_indexes_1502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
        let mut v_entries_1509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
        v_entries_1501_ = lean_ctor_get(v_trailer_1495_, 0);
        lean_inc_ref(v_entries_1501_);
        v_indexes_1502_ = lean_ctor_get(v_trailer_1495_, 1);
        lean_inc_ref(v_indexes_1502_);
        lean_dec_ref(v_trailer_1495_);
        v___x_1503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v___f_1497_,
            v___f_1498_,
            v_indexes_1502_,
            v_name_1496_,
        );
        lean_dec_ref(v_indexes_1502_);
        lean_inc(v___x_1503_);
        v___f_1504_ = lean_alloc_closure(
            l_Std_Http_Trailer_getAll_x3f___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        lean_closure_set(v___f_1504_, 0, v___x_1503_);
        lean_closure_set(v___f_1504_, 1, v_entries_1501_);
        v___x_1505_ = l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9;
        v___x_1506_ = lean_array_get_size(v___x_1503_);
        v___x_1507_ = lean_unsigned_to_nat(0);
        v___x_1508_ = lean_mk_empty_array_with_capacity(v___x_1506_);
        v_entries_1509_ = l_Array_mapFinIdxM_map___redArg(
            v___x_1505_,
            v___x_1503_,
            v___f_1504_,
            v___x_1506_,
            v___x_1507_,
            v___x_1508_,
        );
        v___x_1510_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1510_, 0, v_entries_1509_);
        return v___x_1510_;
    }
}
pub unsafe fn l_Std_Http_Trailer_contains(
    mut v_trailer_1511_: *mut LeanObject,
    mut v_name_1512_: *mut LeanObject,
) -> u8 {
    let mut v_indexes_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    v_indexes_1513_ = lean_ctor_get(v_trailer_1511_, 1);
    v___f_1514_ = l_Std_Http_Trailer_insert___closed__0;
    v___f_1515_ = l_Std_Http_Chunk_instHashableExtensionName___closed__0;
    v___x_1516_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___f_1514_,
        v___f_1515_,
        v_indexes_1513_,
        v_name_1512_,
    );
    return v___x_1516_;
}
pub unsafe fn l_Std_Http_Trailer_contains___boxed(
    mut v_trailer_1517_: *mut LeanObject,
    mut v_name_1518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1519_: u8 = 0;
    let mut v_r_1520_: *mut LeanObject = core::ptr::null_mut();
    v_res_1519_ = l_Std_Http_Trailer_contains(v_trailer_1517_, v_name_1518_);
    lean_dec_ref(v_trailer_1517_);
    v_r_1520_ = lean_box((v_res_1519_) as usize);
    return v_r_1520_;
}
pub unsafe fn l_Std_Http_Trailer_erase___lam__1(
    mut v___f_1521_: *mut LeanObject,
    mut v___f_1522_: *mut LeanObject,
    mut v_x1_1523_: *mut LeanObject,
    mut v_x2_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indexes_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v_i_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indexes_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1525_ = lean_ctor_get(v_x2_1524_, 0);
                lean_inc(v_fst_1525_);
                v_entries_1526_ = lean_ctor_get(v_x1_1523_, 0);
                v_indexes_1527_ = lean_ctor_get(v_x1_1523_, 1);
                v_isSharedCheck_1538_ = (!lean_is_exclusive(v_x1_1523_)) as u8;
                if v_isSharedCheck_1538_ == 0 {
                    v___x_1529_ = v_x1_1523_;
                    v_isShared_1530_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_indexes_1527_);
                    lean_inc(v_entries_1526_);
                    lean_dec(v_x1_1523_);
                    v___x_1529_ = lean_box(0);
                    v_isShared_1530_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_1531_ = lean_array_get_size(v_entries_1526_);
                v_f_1532_ = lean_alloc_closure(
                    l_Std_Http_Trailer_insert___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v_f_1532_, 0, v_i_1531_);
                v_entries_1533_ = lean_array_push(v_entries_1526_, v_x2_1524_);
                v_indexes_1534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_1521_,
                    v___f_1522_,
                    v_indexes_1527_,
                    v_fst_1525_,
                    v_f_1532_,
                );
                if v_isShared_1530_ == 0 {
                    lean_ctor_set(v___x_1529_, 1, v_indexes_1534_);
                    lean_ctor_set(v___x_1529_, 0, v_entries_1533_);
                    v___x_1536_ = v___x_1529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_entries_1533_);
                    lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_indexes_1534_);
                    v___x_1536_ = v_reuseFailAlloc_1537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Trailer_erase___lam__0(
    mut v_name_1539_: *mut LeanObject,
    mut v_x1_1540_: *mut LeanObject,
    mut v_x2_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    v_fst_1542_ = lean_ctor_get(v_x2_1541_, 0);
    v___x_1543_ = lean_string_dec_eq(v_fst_1542_, v_name_1539_);
    if v___x_1543_ == 0 {
        let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
        v___x_1544_ = lean_array_push(v_x1_1540_, v_x2_1541_);
        return v___x_1544_;
    } else {
        lean_dec_ref(v_x2_1541_);
        return v_x1_1540_;
    }
}
pub unsafe fn l_Std_Http_Trailer_erase___lam__0___boxed(
    mut v_name_1545_: *mut LeanObject,
    mut v_x1_1546_: *mut LeanObject,
    mut v_x2_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1548_: *mut LeanObject = core::ptr::null_mut();
    v_res_1548_ = l_Std_Http_Trailer_erase___lam__0(v_name_1545_, v_x1_1546_, v_x2_1547_);
    lean_dec_ref(v_name_1545_);
    return v_res_1548_;
}
pub unsafe fn _init_l_Std_Http_Trailer_erase___closed__1() -> *mut LeanObject {
    let mut v___f_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    v___f_1552_ = l_Std_Http_Chunk_instHashableExtensionName___closed__0;
    v___f_1553_ = l_Std_Http_Trailer_insert___closed__0;
    v___x_1554_ =
        l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_1553_, v___f_1552_);
    return v___x_1554_;
}
pub unsafe fn l_Std_Http_Trailer_erase(
    mut v_trailer_1557_: *mut LeanObject,
    mut v_name_1558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: u8 = 0;
    let mut v_entries_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: usize = 0;
    let mut v___x_1573_: usize = 0;
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: usize = 0;
    let mut v___x_1576_: usize = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___f_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: u8 = 0;
    let mut v___x_1584_: usize = 0;
    let mut v___x_1585_: usize = 0;
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: usize = 0;
    let mut v___x_1588_: usize = 0;
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1559_ = l_Std_Http_Trailer_insert___closed__0;
                v___f_1560_ = l_Std_Http_Chunk_instHashableExtensionName___closed__0;
                lean_inc_ref(v_name_1558_);
                v___x_1561_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v___f_1559_,
                    v___f_1560_,
                    v_name_1558_,
                    v_trailer_1557_,
                );
                if v___x_1561_ == 0 {
                    lean_dec_ref(v_name_1558_);
                    return v_trailer_1557_;
                } else {
                    v_entries_1562_ = lean_ctor_get(v_trailer_1557_, 0);
                    lean_inc_ref(v_entries_1562_);
                    lean_dec_ref(v_trailer_1557_);
                    v___f_1563_ = l_Std_Http_Trailer_erase___closed__0;
                    v___x_1564_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Trailer_erase___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_Trailer_erase___closed__1_once),
                        _init_l_Std_Http_Trailer_erase___closed__1,
                    );
                    v___x_1565_ = lean_unsigned_to_nat(0);
                    v___x_1578_ = lean_array_get_size(v_entries_1562_);
                    v___x_1579_ = l_Std_Http_Trailer_erase___closed__2;
                    v___x_1580_ = l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9;
                    v___x_1581_ = lean_nat_dec_lt(v___x_1565_, v___x_1578_);
                    if v___x_1581_ == 0 {
                        lean_dec_ref(v_entries_1562_);
                        lean_dec_ref(v_name_1558_);
                        v___y_1567_ = v___x_1579_;
                        state = 1;
                        continue;
                    } else {
                        v___f_1582_ = lean_alloc_closure(
                            l_Std_Http_Trailer_erase___lam__0___boxed as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        lean_closure_set(v___f_1582_, 0, v_name_1558_);
                        v___x_1583_ = lean_nat_dec_le(v___x_1578_, v___x_1578_);
                        if v___x_1583_ == 0 {
                            if v___x_1581_ == 0 {
                                lean_dec_ref(v___f_1582_);
                                lean_dec_ref(v_entries_1562_);
                                v___y_1567_ = v___x_1579_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1584_ = 0usize;
                                v___x_1585_ = lean_usize_of_nat(v___x_1578_);
                                v___x_1586_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_1580_,
                                        v___f_1582_,
                                        v_entries_1562_,
                                        v___x_1584_,
                                        v___x_1585_,
                                        v___x_1579_,
                                    );
                                v___y_1567_ = v___x_1586_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1587_ = 0usize;
                            v___x_1588_ = lean_usize_of_nat(v___x_1578_);
                            v___x_1589_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_1580_,
                                    v___f_1582_,
                                    v_entries_1562_,
                                    v___x_1587_,
                                    v___x_1588_,
                                    v___x_1579_,
                                );
                            v___y_1567_ = v___x_1589_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1568_ = lean_array_get_size(v___y_1567_);
                v___x_1569_ = l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9;
                v___x_1570_ = lean_nat_dec_lt(v___x_1565_, v___x_1568_);
                if v___x_1570_ == 0 {
                    lean_dec_ref(v___y_1567_);
                    return v___x_1564_;
                } else {
                    v___x_1571_ = lean_nat_dec_le(v___x_1568_, v___x_1568_);
                    if v___x_1571_ == 0 {
                        if v___x_1570_ == 0 {
                            lean_dec_ref(v___y_1567_);
                            return v___x_1564_;
                        } else {
                            v___x_1572_ = 0usize;
                            v___x_1573_ = lean_usize_of_nat(v___x_1568_);
                            v___x_1574_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_1569_,
                                    v___f_1563_,
                                    v___y_1567_,
                                    v___x_1572_,
                                    v___x_1573_,
                                    v___x_1564_,
                                );
                            return v___x_1574_;
                        }
                    } else {
                        v___x_1575_ = 0usize;
                        v___x_1576_ = lean_usize_of_nat(v___x_1568_);
                        v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_1569_,
                            v___f_1563_,
                            v___y_1567_,
                            v___x_1575_,
                            v___x_1576_,
                            v___x_1564_,
                        );
                        return v___x_1577_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Trailer_size(mut v_trailer_1590_: *mut LeanObject) -> *mut LeanObject {
    let mut v_entries_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    v_entries_1591_ = lean_ctor_get(v_trailer_1590_, 0);
    v___x_1592_ = lean_array_get_size(v_entries_1591_);
    return v___x_1592_;
}
pub unsafe fn l_Std_Http_Trailer_size___boxed(
    mut v_trailer_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1594_: *mut LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Std_Http_Trailer_size(v_trailer_1593_);
    lean_dec_ref(v_trailer_1593_);
    return v_res_1594_;
}
pub unsafe fn l_Std_Http_Trailer_isEmpty(mut v_trailer_1595_: *mut LeanObject) -> u8 {
    let mut v_entries_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    v_entries_1596_ = lean_ctor_get(v_trailer_1595_, 0);
    v___x_1597_ = lean_array_get_size(v_entries_1596_);
    v___x_1598_ = lean_unsigned_to_nat(0);
    v___x_1599_ = lean_nat_dec_eq(v___x_1597_, v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn l_Std_Http_Trailer_isEmpty___boxed(
    mut v_trailer_1600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1601_: u8 = 0;
    let mut v_r_1602_: *mut LeanObject = core::ptr::null_mut();
    v_res_1601_ = l_Std_Http_Trailer_isEmpty(v_trailer_1600_);
    lean_dec_ref(v_trailer_1600_);
    v_r_1602_ = lean_box((v_res_1601_) as usize);
    return v_r_1602_;
}
pub unsafe fn l_Std_Http_Trailer_merge(
    mut v_t1_1603_: *mut LeanObject,
    mut v_t2_1604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    v___x_1605_ = l_Std_Http_Headers_merge(v_t1_1603_, v_t2_1604_);
    return v___x_1605_;
}
pub unsafe fn l_Std_Http_Trailer_merge___boxed(
    mut v_t1_1606_: *mut LeanObject,
    mut v_t2_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1608_: *mut LeanObject = core::ptr::null_mut();
    v_res_1608_ = l_Std_Http_Trailer_merge(v_t1_1606_, v_t2_1607_);
    lean_dec_ref(v_t2_1607_);
    return v_res_1608_;
}
pub unsafe fn l_Std_Http_Trailer_toList(mut v_trailer_1609_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1610_ = l_Std_Http_Headers_toList(v_trailer_1609_);
    return v___x_1610_;
}
pub unsafe fn l_Std_Http_Trailer_toArray(mut v_trailer_1611_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    v___x_1612_ = l_Std_Http_Headers_toArray(v_trailer_1611_);
    return v___x_1612_;
}
pub unsafe fn l_Std_Http_Trailer_toArray___boxed(
    mut v_trailer_1613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1614_: *mut LeanObject = core::ptr::null_mut();
    v_res_1614_ = l_Std_Http_Trailer_toArray(v_trailer_1613_);
    lean_dec_ref(v_trailer_1613_);
    return v_res_1614_;
}
pub unsafe fn l_Std_Http_Trailer_fold___redArg(
    mut v_trailer_1615_: *mut LeanObject,
    mut v_init_1616_: *mut LeanObject,
    mut v_f_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618_ = l_Std_Http_Headers_fold___redArg(v_trailer_1615_, v_init_1616_, v_f_1617_);
    return v___x_1618_;
}
pub unsafe fn l_Std_Http_Trailer_fold___redArg___boxed(
    mut v_trailer_1619_: *mut LeanObject,
    mut v_init_1620_: *mut LeanObject,
    mut v_f_1621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1622_: *mut LeanObject = core::ptr::null_mut();
    v_res_1622_ = l_Std_Http_Trailer_fold___redArg(v_trailer_1619_, v_init_1620_, v_f_1621_);
    lean_dec_ref(v_trailer_1619_);
    return v_res_1622_;
}
pub unsafe fn l_Std_Http_Trailer_fold(
    mut v_00_u03b1_1623_: *mut LeanObject,
    mut v_trailer_1624_: *mut LeanObject,
    mut v_init_1625_: *mut LeanObject,
    mut v_f_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Std_Http_Headers_fold___redArg(v_trailer_1624_, v_init_1625_, v_f_1626_);
    return v___x_1627_;
}
pub unsafe fn l_Std_Http_Trailer_fold___boxed(
    mut v_00_u03b1_1628_: *mut LeanObject,
    mut v_trailer_1629_: *mut LeanObject,
    mut v_init_1630_: *mut LeanObject,
    mut v_f_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1632_: *mut LeanObject = core::ptr::null_mut();
    v_res_1632_ =
        l_Std_Http_Trailer_fold(v_00_u03b1_1628_, v_trailer_1629_, v_init_1630_, v_f_1631_);
    lean_dec_ref(v_trailer_1629_);
    return v_res_1632_;
}
pub unsafe fn l_Std_Http_Trailer_instEncodeV11___lam__0(
    mut v___x_1633_: *mut LeanObject,
    mut v___x_1634_: *mut LeanObject,
    mut v___x_1635_: *mut LeanObject,
    mut v_name_1636_: *mut LeanObject,
    mut v___x_1637_: *mut LeanObject,
    mut v___x_1638_: u32,
    mut v___x_1639_: *mut LeanObject,
    mut v_it_1640_: *mut LeanObject,
    mut v_acc_1641_: *mut LeanObject,
    mut v_hP_1642_: *mut LeanObject,
    mut v_recur_1643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1652_: u8 = 0;
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut v_it_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u32 = 0;
    let mut v___x_1667_: u32 = 0;
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: u32 = 0;
    let mut v___x_1671_: u8 = 0;
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u32 = 0;
    let mut v___x_1674_: u32 = 0;
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___x_1681_: u8 = 0;
    let mut v___x_1682_: u32 = 0;
    let mut v___x_1683_: u8 = 0;
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_it_1640_) == 0 {
                    v_currPos_1676_ = lean_ctor_get(v_it_1640_, 0);
                    v_searcher_1677_ = lean_ctor_get(v_it_1640_, 1);
                    v_isSharedCheck_1699_ = (!lean_is_exclusive(v_it_1640_)) as u8;
                    if v_isSharedCheck_1699_ == 0 {
                        v___x_1679_ = v_it_1640_;
                        v_isShared_1680_ = v_isSharedCheck_1699_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_searcher_1677_);
                        lean_inc(v_currPos_1676_);
                        lean_dec(v_it_1640_);
                        v___x_1679_ = lean_box(0);
                        v_isShared_1680_ = v_isSharedCheck_1699_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_recur_1643_);
                    lean_dec(v___x_1637_);
                    return v_acc_1641_;
                }
            }
            1 => {
                if lean_obj_tag(v_acc_1641_) == 0 {
                    v___x_1647_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1647_, 0, v_out_1646_);
                    v___x_1648_ = lean_apply_4(
                        v_recur_1643_,
                        v_it_1645_,
                        v___x_1647_,
                        lean_box(0),
                        lean_box(0),
                    );
                    return v___x_1648_;
                } else {
                    v_val_1649_ = lean_ctor_get(v_acc_1641_, 0);
                    v_isSharedCheck_1660_ = (!lean_is_exclusive(v_acc_1641_)) as u8;
                    if v_isSharedCheck_1660_ == 0 {
                        v___x_1651_ = v_acc_1641_;
                        v_isShared_1652_ = v_isSharedCheck_1660_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1649_);
                        lean_dec(v_acc_1641_);
                        v___x_1651_ = lean_box(0);
                        v_isShared_1652_ = v_isSharedCheck_1660_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1653_ = lean_string_utf8_extract(v___x_1633_, v___x_1634_, v___x_1635_);
                v___x_1654_ = lean_string_append(v_val_1649_, v___x_1653_);
                lean_dec_ref(v___x_1653_);
                v___x_1655_ = lean_string_append(v___x_1654_, v_out_1646_);
                lean_dec_ref(v_out_1646_);
                if v_isShared_1652_ == 0 {
                    lean_ctor_set(v___x_1651_, 0, v___x_1655_);
                    v___x_1657_ = v___x_1651_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1655_);
                    v___x_1657_ = v_reuseFailAlloc_1659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1658_ = lean_apply_4(
                    v_recur_1643_,
                    v_it_1645_,
                    v___x_1657_,
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_1658_;
            }
            4 => {
                v___x_1665_ = lean_string_utf8_extract(
                    v_name_1636_,
                    v_startInclusive_1663_,
                    v_endExclusive_1664_,
                );
                lean_dec(v_endExclusive_1664_);
                lean_dec(v_startInclusive_1663_);
                v___x_1666_ = lean_string_utf8_get(v___x_1665_, v___x_1634_);
                v___x_1667_ = 97;
                v___x_1668_ = lean_uint32_dec_le(v___x_1667_, v___x_1666_);
                if v___x_1668_ == 0 {
                    v___x_1669_ = lean_string_utf8_set(v___x_1665_, v___x_1634_, v___x_1666_);
                    v_it_1645_ = v_it_1662_;
                    v_out_1646_ = v___x_1669_;
                    state = 1;
                    continue;
                } else {
                    v___x_1670_ = 122;
                    v___x_1671_ = lean_uint32_dec_le(v___x_1666_, v___x_1670_);
                    if v___x_1671_ == 0 {
                        v___x_1672_ = lean_string_utf8_set(v___x_1665_, v___x_1634_, v___x_1666_);
                        v_it_1645_ = v_it_1662_;
                        v_out_1646_ = v___x_1672_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1673_ = 4294967264;
                        v___x_1674_ = lean_uint32_add(v___x_1666_, v___x_1673_);
                        v___x_1675_ = lean_string_utf8_set(v___x_1665_, v___x_1634_, v___x_1674_);
                        v_it_1645_ = v_it_1662_;
                        v_out_1646_ = v___x_1675_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1681_ = lean_nat_dec_eq(v_searcher_1677_, v___x_1637_);
                if v___x_1681_ == 0 {
                    lean_dec(v___x_1637_);
                    v___x_1682_ = lean_string_utf8_get_fast(v_name_1636_, v_searcher_1677_);
                    v___x_1683_ = lean_uint32_dec_eq(v___x_1682_, v___x_1638_);
                    if v___x_1683_ == 0 {
                        v___x_1684_ = lean_string_utf8_next_fast(v_name_1636_, v_searcher_1677_);
                        lean_dec(v_searcher_1677_);
                        if v_isShared_1680_ == 0 {
                            lean_ctor_set(v___x_1679_, 1, v___x_1684_);
                            v___x_1686_ = v___x_1679_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_currPos_1676_);
                            lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1684_);
                            v___x_1686_ = v_reuseFailAlloc_1688_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_1689_ = lean_string_utf8_next_fast(v_name_1636_, v_searcher_1677_);
                        v___x_1690_ = lean_nat_sub(v___x_1689_, v_searcher_1677_);
                        v___x_1691_ = lean_nat_add(v_searcher_1677_, v___x_1690_);
                        lean_dec(v___x_1690_);
                        v_slice_1692_ = l_String_Slice_subslice_x21(
                            v___x_1639_,
                            v_currPos_1676_,
                            v_searcher_1677_,
                        );
                        lean_inc(v___x_1691_);
                        if v_isShared_1680_ == 0 {
                            lean_ctor_set(v___x_1679_, 1, v___x_1691_);
                            lean_ctor_set(v___x_1679_, 0, v___x_1691_);
                            v_nextIt_1694_ = v___x_1679_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1691_);
                            lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1691_);
                            v_nextIt_1694_ = v_reuseFailAlloc_1697_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1679_);
                    lean_dec(v_searcher_1677_);
                    v___x_1698_ = lean_box(1);
                    v_it_1662_ = v___x_1698_;
                    v_startInclusive_1663_ = v_currPos_1676_;
                    v_endExclusive_1664_ = v___x_1637_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_1687_ = lean_apply_4(
                    v_recur_1643_,
                    v___x_1686_,
                    v_acc_1641_,
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_1687_;
            }
            7 => {
                v_startInclusive_1695_ = lean_ctor_get(v_slice_1692_, 0);
                lean_inc(v_startInclusive_1695_);
                v_endExclusive_1696_ = lean_ctor_get(v_slice_1692_, 1);
                lean_inc(v_endExclusive_1696_);
                lean_dec_ref(v_slice_1692_);
                v_it_1662_ = v_nextIt_1694_;
                v_startInclusive_1663_ = v_startInclusive_1695_;
                v_endExclusive_1664_ = v_endExclusive_1696_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Trailer_instEncodeV11___lam__0___boxed(
    mut v___x_1700_: *mut LeanObject,
    mut v___x_1701_: *mut LeanObject,
    mut v___x_1702_: *mut LeanObject,
    mut v_name_1703_: *mut LeanObject,
    mut v___x_1704_: *mut LeanObject,
    mut v___x_1705_: *mut LeanObject,
    mut v___x_1706_: *mut LeanObject,
    mut v_it_1707_: *mut LeanObject,
    mut v_acc_1708_: *mut LeanObject,
    mut v_hP_1709_: *mut LeanObject,
    mut v_recur_1710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_635__boxed_1711_: u32 = 0;
    let mut v_res_1712_: *mut LeanObject = core::ptr::null_mut();
    v___x_635__boxed_1711_ = lean_unbox_uint32(v___x_1705_);
    lean_dec(v___x_1705_);
    v_res_1712_ = l_Std_Http_Trailer_instEncodeV11___lam__0(
        v___x_1700_,
        v___x_1701_,
        v___x_1702_,
        v_name_1703_,
        v___x_1704_,
        v___x_635__boxed_1711_,
        v___x_1706_,
        v_it_1707_,
        v_acc_1708_,
        v_hP_1709_,
        v_recur_1710_,
    );
    lean_dec_ref(v___x_1706_);
    lean_dec_ref(v_name_1703_);
    lean_dec(v___x_1702_);
    lean_dec(v___x_1701_);
    lean_dec_ref(v___x_1700_);
    return v_res_1712_;
}
pub unsafe fn _init_l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2;
    v___x_1717_ = lean_string_utf8_byte_size(v___x_1716_);
    return v___x_1717_;
}
pub unsafe fn _init_l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1() -> *mut LeanObject
{
    let mut v___x_1718_: u32 = 0;
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1718_ = 45;
    v___x_1719_ = lean_box_uint32(v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn l_Std_Http_Trailer_instEncodeV11___lam__1(
    mut v_buf_1720_: *mut LeanObject,
    mut v_name_1721_: *mut LeanObject,
    mut v_value_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut v___f_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1743_ = l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1;
                v___x_1744_ = lean_unsigned_to_nat(0);
                v___x_1745_ = lean_string_utf8_byte_size(v_name_1721_);
                lean_inc_ref(v_name_1721_);
                v___x_1746_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1746_, 0, v_name_1721_);
                lean_ctor_set(v___x_1746_, 1, v___x_1744_);
                lean_ctor_set(v___x_1746_, 2, v___x_1745_);
                lean_inc_ref(v___x_1746_);
                v_it_1747_ = l_String_Slice_splitToSubslice___redArg(v___x_1746_, v___f_1743_);
                v___x_1748_ = l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2;
                v___x_1749_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3_once
                    ),
                    _init_l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3,
                );
                v___x_1750_ = l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1;
                v___f_1751_ = lean_alloc_closure(
                    l_Std_Http_Trailer_instEncodeV11___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    7,
                );
                lean_closure_set(v___f_1751_, 0, v___x_1748_);
                lean_closure_set(v___f_1751_, 1, v___x_1744_);
                lean_closure_set(v___f_1751_, 2, v___x_1749_);
                lean_closure_set(v___f_1751_, 3, v_name_1721_);
                lean_closure_set(v___f_1751_, 4, v___x_1745_);
                lean_closure_set(v___f_1751_, 5, v___x_1750_);
                lean_closure_set(v___f_1751_, 6, v___x_1746_);
                v___x_1752_ = lean_box(0);
                v___x_1753_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1751_,
                    v_it_1747_,
                    v___x_1752_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1753_) == 0 {
                    v___x_1754_ = l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0;
                    v___y_1724_ = v___x_1754_;
                    state = 1;
                    continue;
                } else {
                    v_val_1755_ = lean_ctor_get(v___x_1753_, 0);
                    lean_inc(v_val_1755_);
                    lean_dec_ref_known(v___x_1753_, 1);
                    v___y_1724_ = v_val_1755_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_1725_ = lean_ctor_get(v_buf_1720_, 0);
                v_size_1726_ = lean_ctor_get(v_buf_1720_, 1);
                v_isSharedCheck_1742_ = (!lean_is_exclusive(v_buf_1720_)) as u8;
                if v_isSharedCheck_1742_ == 0 {
                    v___x_1728_ = v_buf_1720_;
                    v_isShared_1729_ = v_isSharedCheck_1742_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_size_1726_);
                    lean_inc(v_data_1725_);
                    lean_dec(v_buf_1720_);
                    v___x_1728_ = lean_box(0);
                    v_isShared_1729_ = v_isSharedCheck_1742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1730_ = l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0;
                v___x_1731_ = lean_string_append(v___y_1724_, v___x_1730_);
                v___x_1732_ = lean_string_append(v___x_1731_, v_value_1722_);
                v___x_1733_ = l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10;
                v___x_1734_ = lean_string_append(v___x_1732_, v___x_1733_);
                v___x_1735_ = lean_string_to_utf8(v___x_1734_);
                lean_dec_ref(v___x_1734_);
                lean_inc_ref(v___x_1735_);
                v___x_1736_ = lean_array_push(v_data_1725_, v___x_1735_);
                v___x_1737_ = lean_byte_array_size(v___x_1735_);
                lean_dec_ref(v___x_1735_);
                v___x_1738_ = lean_nat_add(v_size_1726_, v___x_1737_);
                lean_dec(v_size_1726_);
                if v_isShared_1729_ == 0 {
                    lean_ctor_set(v___x_1728_, 1, v___x_1738_);
                    lean_ctor_set(v___x_1728_, 0, v___x_1736_);
                    v___x_1740_ = v___x_1728_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1736_);
                    lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1738_);
                    v___x_1740_ = v_reuseFailAlloc_1741_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Trailer_instEncodeV11___lam__1___boxed(
    mut v_buf_1756_: *mut LeanObject,
    mut v_name_1757_: *mut LeanObject,
    mut v_value_1758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1759_: *mut LeanObject = core::ptr::null_mut();
    v_res_1759_ =
        l_Std_Http_Trailer_instEncodeV11___lam__1(v_buf_1756_, v_name_1757_, v_value_1758_);
    lean_dec_ref(v_value_1758_);
    return v_res_1759_;
}
pub unsafe fn _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1() -> *mut LeanObject {
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    v___x_1761_ = l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0;
    v___x_1762_ = lean_string_to_utf8(v___x_1761_);
    return v___x_1762_;
}
pub unsafe fn _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2() -> *mut LeanObject {
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    v___x_1763_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once),
        _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1,
    );
    v___x_1764_ = lean_byte_array_size(v___x_1763_);
    return v___x_1764_;
}
pub unsafe fn _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3() -> *mut LeanObject {
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    v___x_1765_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11),
        core::ptr::addr_of_mut!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once),
        _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11,
    );
    v___x_1766_ = lean_byte_array_size(v___x_1765_);
    return v___x_1766_;
}
pub unsafe fn l_Std_Http_Trailer_instEncodeV11___lam__2(
    mut v___f_1767_: *mut LeanObject,
    mut v_buffer_1768_: *mut LeanObject,
    mut v_trailer_1769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut v_reuseFailAlloc_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_1770_ = lean_ctor_get(v_buffer_1768_, 0);
                v_size_1771_ = lean_ctor_get(v_buffer_1768_, 1);
                v_isSharedCheck_1796_ = (!lean_is_exclusive(v_buffer_1768_)) as u8;
                if v_isSharedCheck_1796_ == 0 {
                    v___x_1773_ = v_buffer_1768_;
                    v_isShared_1774_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_size_1771_);
                    lean_inc(v_data_1770_);
                    lean_dec(v_buffer_1768_);
                    v___x_1773_ = lean_box(0);
                    v_isShared_1774_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1775_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once
                    ),
                    _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1,
                );
                v___x_1776_ = lean_array_push(v_data_1770_, v___x_1775_);
                v___x_1777_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2_once
                    ),
                    _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2,
                );
                v___x_1778_ = lean_nat_add(v_size_1771_, v___x_1777_);
                lean_dec(v_size_1771_);
                if v_isShared_1774_ == 0 {
                    lean_ctor_set(v___x_1773_, 1, v___x_1778_);
                    lean_ctor_set(v___x_1773_, 0, v___x_1776_);
                    v___x_1780_ = v___x_1773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1776_);
                    lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___x_1778_);
                    v___x_1780_ = v_reuseFailAlloc_1795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1781_ =
                    l_Std_Http_Headers_fold___redArg(v_trailer_1769_, v___x_1780_, v___f_1767_);
                v_data_1782_ = lean_ctor_get(v___x_1781_, 0);
                v_size_1783_ = lean_ctor_get(v___x_1781_, 1);
                v_isSharedCheck_1794_ = (!lean_is_exclusive(v___x_1781_)) as u8;
                if v_isSharedCheck_1794_ == 0 {
                    v___x_1785_ = v___x_1781_;
                    v_isShared_1786_ = v_isSharedCheck_1794_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_size_1783_);
                    lean_inc(v_data_1782_);
                    lean_dec(v___x_1781_);
                    v___x_1785_ = lean_box(0);
                    v_isShared_1786_ = v_isSharedCheck_1794_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1787_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once
                    ),
                    _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11,
                );
                v___x_1788_ = lean_array_push(v_data_1782_, v___x_1787_);
                v___x_1789_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3_once
                    ),
                    _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3,
                );
                v___x_1790_ = lean_nat_add(v_size_1783_, v___x_1789_);
                lean_dec(v_size_1783_);
                if v_isShared_1786_ == 0 {
                    lean_ctor_set(v___x_1785_, 1, v___x_1790_);
                    lean_ctor_set(v___x_1785_, 0, v___x_1788_);
                    v___x_1792_ = v___x_1785_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1788_);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1790_);
                    v___x_1792_ = v_reuseFailAlloc_1793_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Trailer_instEncodeV11___lam__2___boxed(
    mut v___f_1797_: *mut LeanObject,
    mut v_buffer_1798_: *mut LeanObject,
    mut v_trailer_1799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1800_: *mut LeanObject = core::ptr::null_mut();
    v_res_1800_ =
        l_Std_Http_Trailer_instEncodeV11___lam__2(v___f_1797_, v_buffer_1798_, v_trailer_1799_);
    lean_dec_ref(v_trailer_1799_);
    return v_res_1800_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Chunk(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Http_instInhabitedChunk_default = _init_l_Std_Http_instInhabitedChunk_default();
    lean_mark_persistent(l_Std_Http_instInhabitedChunk_default);
    l_Std_Http_instInhabitedChunk = _init_l_Std_Http_instInhabitedChunk();
    lean_mark_persistent(l_Std_Http_instInhabitedChunk);
    l_Std_Http_Chunk_empty = _init_l_Std_Http_Chunk_empty();
    lean_mark_persistent(l_Std_Http_Chunk_empty);
    l_Std_Http_instInhabitedTrailer_default = _init_l_Std_Http_instInhabitedTrailer_default();
    lean_mark_persistent(l_Std_Http_instInhabitedTrailer_default);
    l_Std_Http_instInhabitedTrailer = _init_l_Std_Http_instInhabitedTrailer();
    lean_mark_persistent(l_Std_Http_instInhabitedTrailer);
    l_Std_Http_Trailer_empty = _init_l_Std_Http_Trailer_empty();
    lean_mark_persistent(l_Std_Http_Trailer_empty);
    l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1 =
        _init_l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1();
    lean_mark_persistent(l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Chunk(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Std_Http_Internal_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam =
        _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam();
    lean_mark_persistent(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam);
    l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam =
        _init_l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam();
    lean_mark_persistent(l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Chunk(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Data_Headers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Internal_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Chunk(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Chunk(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Data_Chunk(builtin);
}
