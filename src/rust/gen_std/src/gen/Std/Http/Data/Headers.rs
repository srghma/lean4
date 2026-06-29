// Lean compiler output
// Module: Std.Http.Data.Headers
// Imports: Std.Http.Data.Headers.Basic Std.Http.Data.Headers.Name Std.Http.Data.Headers.Value
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_byte_array_size, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_nat_to_int, lean_string_append,
    lean_string_dec_eq, lean_string_hash, lean_string_length, lean_string_to_utf8,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_string_utf8_set, lean_uint32_add,
    lean_uint32_dec_eq, lean_uint32_dec_le, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_mapFinIdxM_map___redArg,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Pattern::Char::l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_splitToSubslice___redArg;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Prelude::{
    l_String_decEq___boxed, l_String_hash___boxed, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
};
use crate::r#gen::Std::Http::Data::Headers::Basic::{
    initialize_Std_Http_Data_Headers_Basic, runtime_initialize_Std_Http_Data_Headers_Basic,
};
use crate::r#gen::Std::Http::Data::Headers::Name::{
    initialize_Std_Http_Data_Headers_Name, l_Std_Http_Header_Name_ofString_x3f,
    l_Std_Http_Header_Name_ofString_x21, l_Std_Http_Header_instReprName_repr___redArg,
    runtime_initialize_Std_Http_Data_Headers_Name,
};
use crate::r#gen::Std::Http::Data::Headers::Value::{
    initialize_Std_Http_Data_Headers_Value, l_Std_Http_Header_Value_ofString_x3f,
    l_Std_Http_Header_Value_ofString_x21, l_Std_Http_Header_instBEqValue_beq,
    l_Std_Http_Header_instReprValue_repr___redArg, runtime_initialize_Std_Http_Data_Headers_Value,
};
use crate::r#gen::Std::Http::Internal::IndexMultiMap::{
    l_Std_Internal_IndexMultiMap_empty, l_Std_Internal_IndexMultiMap_instDecidableMem___redArg,
};
pub static l_Std_Http_instInhabitedHeaders_default___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Http_instInhabitedHeaders_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instInhabitedHeaders_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_instInhabitedHeaders_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instInhabitedHeaders_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_instInhabitedHeaders_default___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instInhabitedHeaders_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_instInhabitedHeaders_default___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instInhabitedHeaders_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_instInhabitedHeaders_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_instInhabitedHeaders: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 110, 116, 114, 105, 101, 115, 0]};
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [123, 32, 0]};
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 110, 100, 101, 120, 101, 115, 0]};
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [83, 116, 100, 46, 72, 97, 115, 104, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32, 0]};
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [118, 97, 108, 105, 100, 105, 116, 121, 0]};
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 125, 0]};
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprHeaders_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 97, 112, 0],
};
static mut l_Std_Http_instReprHeaders_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprHeaders_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprHeaders_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instReprHeaders_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprHeaders_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprHeaders_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprHeaders_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_instReprHeaders_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_instReprHeaders_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprHeaders_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instReprHeaders_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Std_Http_instReprHeaders_repr___redArg___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Http_instReprHeaders_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprHeaders_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_instReprHeaders_repr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_instReprHeaders_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_instReprHeaders___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_instReprHeaders_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instReprHeaders___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprHeaders___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instReprHeaders: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instReprHeaders___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instMembershipNameHeaders: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_instDecidableMemNameHeaders___closed__0_value:
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
    m_fun: l_String_decEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_instDecidableMemNameHeaders___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instDecidableMemNameHeaders___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instDecidableMemNameHeaders___closed__1_value:
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
    m_fun: l_String_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_instDecidableMemNameHeaders___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instDecidableMemNameHeaders___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Headers_getAll___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Headers_getAll___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Headers_getAll___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Headers_getAll___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__4_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Headers_getAll___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__5_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Headers_getAll___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__6_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Headers_getAll___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Headers_getAll___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Headers_getAll___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_getAll___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Headers_getAll___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_getAll___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_hasEntry___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Headers_hasEntry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_hasEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_get_x21___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Headers_get_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_get_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_get_x21___closed__1_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Std_Http_Headers_get_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_get_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_get_x21___closed__2_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
    };
static mut l_Std_Http_Headers_get_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_get_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_get_x21___closed__3_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_Std_Http_Headers_get_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_get_x21___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Headers_get_x21___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Headers_get_x21___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Headers_empty___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Headers_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Headers_empty: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Headers_erase___closed__0_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Headers_erase___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instDecidableMemNameHeaders___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_instDecidableMemNameHeaders___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Headers_erase___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_erase___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Headers_erase___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Headers_erase___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Headers_instToString___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Http_Headers_instToString___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instToString___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_instToString___lam__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Http_Headers_instToString___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instToString___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_instToString___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Http_Headers_instToString___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instToString___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Headers_instToString___lam__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Headers_instToString___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Headers_instToString___lam__1___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Headers_instToString___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Http_Headers_instToString___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instToString___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Headers_instToString___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Headers_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_instToString___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Headers_instToString___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Headers_instToString___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Headers_instToString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instToString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Headers_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instToString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_instEncodeV11___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Headers_instEncodeV11___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Headers_instEncodeV11___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instEncodeV11___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_instEncodeV11___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Headers_instEncodeV11___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Headers_instEncodeV11___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Headers_instEncodeV11___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instEncodeV11___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Headers_instEncodeV11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instEncodeV11___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Headers_instEmptyCollection: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value:
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
    m_fun: l_Std_Http_Headers_instSingletonProdNameValue___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Headers_instSingletonProdNameValue___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Headers_instSingletonProdNameValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_instInsertProdNameValue___closed__0_value:
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
    m_fun: l_Std_Http_Headers_instInsertProdNameValue___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Headers_instInsertProdNameValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instInsertProdNameValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Headers_instInsertProdNameValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instInsertProdNameValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Headers_instUnion___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Headers_merge___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Headers_instUnion___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instUnion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Headers_instUnion: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Headers_instUnion___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Http_instInhabitedHeaders_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = crate::leanh::lean_box(0);
    v___x_1859_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1860_ = lean_mk_array(v___x_1859_, v___x_1858_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedHeaders_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedHeaders_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedHeaders_default___closed__1_once),
        _init_l_Std_Http_instInhabitedHeaders_default___closed__1,
    );
    v___x_1862_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    return v___x_1863_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedHeaders_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedHeaders_default___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedHeaders_default___closed__2_once),
        _init_l_Std_Http_instInhabitedHeaders_default___closed__2,
    );
    v___x_1865_ = l_Std_Http_instInhabitedHeaders_default___closed__0;
    v___x_1866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1865_);
    crate::leanh::lean_ctor_set(v___x_1866_, 1, v___x_1864_);
    return v___x_1866_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedHeaders_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedHeaders_default___closed__3),
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedHeaders_default___closed__3_once),
        _init_l_Std_Http_instInhabitedHeaders_default___closed__3,
    );
    return v___x_1867_;
}
pub unsafe fn _init_l_Std_Http_instInhabitedHeaders() -> *mut crate::leanh::LeanObject {
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l_Std_Http_instInhabitedHeaders_default;
    return v___x_1868_;
}
pub unsafe fn l_Nat_cast___at___00Std_Http_instReprHeaders_repr_spec__1(
    mut v_a_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = lean_nat_to_int(v_a_1869_);
    return v___x_1870_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15_spec__17(
    mut v_x_1871_: *mut crate::leanh::LeanObject,
    mut v_x_1872_: *mut crate::leanh::LeanObject,
    mut v_x_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1878_: u8 = 0;
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1873_) == 0 {
                    crate::leanh::lean_dec(v_x_1871_);
                    return v_x_1872_;
                } else {
                    v_head_1874_ = crate::leanh::lean_ctor_get(v_x_1873_, 0);
                    v_tail_1875_ = crate::leanh::lean_ctor_get(v_x_1873_, 1);
                    v_isSharedCheck_1886_ = (!crate::leanh::lean_is_exclusive(v_x_1873_)) as u8;
                    if v_isSharedCheck_1886_ == 0 {
                        v___x_1877_ = v_x_1873_;
                        v_isShared_1878_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1875_);
                        crate::leanh::lean_inc(v_head_1874_);
                        crate::leanh::lean_dec(v_x_1873_);
                        v___x_1877_ = crate::leanh::lean_box(0);
                        v_isShared_1878_ = v_isSharedCheck_1886_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1871_);
                if v_isShared_1878_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1877_, 5);
                    crate::leanh::lean_ctor_set(v___x_1877_, 1, v_x_1871_);
                    crate::leanh::lean_ctor_set(v___x_1877_, 0, v_x_1872_);
                    v___x_1880_ = v___x_1877_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1885_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_x_1872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_x_1871_);
                    v___x_1880_ = v_reuseFailAlloc_1885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1881_ = l_Nat_reprFast(v_head_1874_);
                v___x_1882_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
                v___x_1883_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1883_, 0, v___x_1880_);
                crate::leanh::lean_ctor_set(v___x_1883_, 1, v___x_1882_);
                v_x_1872_ = v___x_1883_;
                v_x_1873_ = v_tail_1875_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15(
    mut v_x_1887_: *mut crate::leanh::LeanObject,
    mut v_x_1888_: *mut crate::leanh::LeanObject,
    mut v_x_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1894_: u8 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1889_) == 0 {
                    crate::leanh::lean_dec(v_x_1887_);
                    return v_x_1888_;
                } else {
                    v_head_1890_ = crate::leanh::lean_ctor_get(v_x_1889_, 0);
                    v_tail_1891_ = crate::leanh::lean_ctor_get(v_x_1889_, 1);
                    v_isSharedCheck_1902_ = (!crate::leanh::lean_is_exclusive(v_x_1889_)) as u8;
                    if v_isSharedCheck_1902_ == 0 {
                        v___x_1893_ = v_x_1889_;
                        v_isShared_1894_ = v_isSharedCheck_1902_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1891_);
                        crate::leanh::lean_inc(v_head_1890_);
                        crate::leanh::lean_dec(v_x_1889_);
                        v___x_1893_ = crate::leanh::lean_box(0);
                        v_isShared_1894_ = v_isSharedCheck_1902_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1887_);
                if v_isShared_1894_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1893_, 5);
                    crate::leanh::lean_ctor_set(v___x_1893_, 1, v_x_1887_);
                    crate::leanh::lean_ctor_set(v___x_1893_, 0, v_x_1888_);
                    v___x_1896_ = v___x_1893_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_x_1888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_x_1887_);
                    v___x_1896_ = v_reuseFailAlloc_1901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1897_ = l_Nat_reprFast(v_head_1890_);
                v___x_1898_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1898_, 0, v___x_1897_);
                v___x_1899_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1899_, 0, v___x_1896_);
                crate::leanh::lean_ctor_set(v___x_1899_, 1, v___x_1898_);
                v___x_1900_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15_spec__17(v_x_1887_, v___x_1899_, v_tail_1891_);
                return v___x_1900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(
    mut v___y_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1904_ = l_Nat_reprFast(v___y_1903_);
    v___x_1905_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
    return v___x_1905_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13(
    mut v_x_1906_: *mut crate::leanh::LeanObject,
    mut v_x_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1906_) == 0 {
        let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1907_);
        v___x_1908_ = crate::leanh::lean_box(0);
        return v___x_1908_;
    } else {
        let mut v_tail_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1909_ = crate::leanh::lean_ctor_get(v_x_1906_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1909_) == 0 {
            let mut v_head_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1907_);
            v_head_1910_ = crate::leanh::lean_ctor_get(v_x_1906_, 0);
            crate::leanh::lean_inc(v_head_1910_);
            crate::leanh::lean_dec_ref_known(v_x_1906_, 2);
            v___x_1911_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(v_head_1910_);
            return v___x_1911_;
        } else {
            let mut v_head_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1909_);
            v_head_1912_ = crate::leanh::lean_ctor_get(v_x_1906_, 0);
            crate::leanh::lean_inc(v_head_1912_);
            crate::leanh::lean_dec_ref_known(v_x_1906_, 2);
            v___x_1913_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(v_head_1912_);
            v___x_1914_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15(v_x_1907_, v___x_1913_, v_tail_1909_);
            return v___x_1914_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0;
    v___x_1924_ = lean_string_length(v___x_1923_);
    return v___x_1924_;
}
pub unsafe fn _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5), core::ptr::addr_of_mut!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5_once), _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5);
    v___x_1926_ = lean_nat_to_int(v___x_1925_);
    return v___x_1926_;
}
pub unsafe fn l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8(
    mut v_xs_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: u8 = 0;
    v___x_1935_ = lean_array_get_size(v_xs_1934_);
    v___x_1936_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1937_ = lean_nat_dec_eq(v___x_1935_, v___x_1936_);
    if v___x_1937_ == 0 {
        let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1938_ = lean_array_to_list(v_xs_1934_);
        v___x_1939_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3;
        v___x_1940_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13(v___x_1938_, v___x_1939_);
        v___x_1941_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6_once), _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6);
        v___x_1942_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7;
        v___x_1943_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1942_);
        crate::leanh::lean_ctor_set(v___x_1943_, 1, v___x_1940_);
        v___x_1944_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8;
        v___x_1945_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1945_, 0, v___x_1943_);
        crate::leanh::lean_ctor_set(v___x_1945_, 1, v___x_1944_);
        v___x_1946_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1946_, 0, v___x_1941_);
        crate::leanh::lean_ctor_set(v___x_1946_, 1, v___x_1945_);
        v___x_1947_ = l_Std_Format_fill(v___x_1946_);
        return v___x_1947_;
    } else {
        let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_1934_);
        v___x_1948_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10;
        return v___x_1948_;
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__7(
    mut v_x_1949_: *mut crate::leanh::LeanObject,
    mut v_x_1950_: *mut crate::leanh::LeanObject,
    mut v_x_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1956_: u8 = 0;
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1951_) == 0 {
                    crate::leanh::lean_dec(v_x_1949_);
                    return v_x_1950_;
                } else {
                    v_head_1952_ = crate::leanh::lean_ctor_get(v_x_1951_, 0);
                    v_tail_1953_ = crate::leanh::lean_ctor_get(v_x_1951_, 1);
                    v_isSharedCheck_1962_ = (!crate::leanh::lean_is_exclusive(v_x_1951_)) as u8;
                    if v_isSharedCheck_1962_ == 0 {
                        v___x_1955_ = v_x_1951_;
                        v_isShared_1956_ = v_isSharedCheck_1962_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1953_);
                        crate::leanh::lean_inc(v_head_1952_);
                        crate::leanh::lean_dec(v_x_1951_);
                        v___x_1955_ = crate::leanh::lean_box(0);
                        v_isShared_1956_ = v_isSharedCheck_1962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1949_);
                if v_isShared_1956_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1955_, 5);
                    crate::leanh::lean_ctor_set(v___x_1955_, 1, v_x_1949_);
                    crate::leanh::lean_ctor_set(v___x_1955_, 0, v_x_1950_);
                    v___x_1958_ = v___x_1955_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1961_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_x_1950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_x_1949_);
                    v___x_1958_ = v_reuseFailAlloc_1961_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1959_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1959_, 0, v___x_1958_);
                crate::leanh::lean_ctor_set(v___x_1959_, 1, v_head_1952_);
                v_x_1950_ = v___x_1959_;
                v_x_1951_ = v_tail_1953_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_1963_: *mut crate::leanh::LeanObject,
    mut v_x_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1963_) == 0 {
        let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1964_);
        v___x_1965_ = crate::leanh::lean_box(0);
        return v___x_1965_;
    } else {
        let mut v_tail_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1966_ = crate::leanh::lean_ctor_get(v_x_1963_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1966_) == 0 {
            let mut v_head_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1964_);
            v_head_1967_ = crate::leanh::lean_ctor_get(v_x_1963_, 0);
            crate::leanh::lean_inc(v_head_1967_);
            crate::leanh::lean_dec_ref_known(v_x_1963_, 2);
            return v_head_1967_;
        } else {
            let mut v_head_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1966_);
            v_head_1968_ = crate::leanh::lean_ctor_get(v_x_1963_, 0);
            crate::leanh::lean_inc(v_head_1968_);
            crate::leanh::lean_dec_ref_known(v_x_1963_, 2);
            v___x_1969_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__7(v_x_1964_, v_head_1968_, v_tail_1966_);
            return v___x_1969_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0;
    v___x_1973_ = lean_string_length(v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1974_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2_once), _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2);
    v___x_1975_ = lean_nat_to_int(v___x_1974_);
    return v___x_1975_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(
    mut v_x_1980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u8 = 0;
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1981_ = crate::leanh::lean_ctor_get(v_x_1980_, 0);
                v_snd_1982_ = crate::leanh::lean_ctor_get(v_x_1980_, 1);
                v_isSharedCheck_2004_ = (!crate::leanh::lean_is_exclusive(v_x_1980_)) as u8;
                if v_isSharedCheck_2004_ == 0 {
                    v___x_1984_ = v_x_1980_;
                    v_isShared_1985_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1982_);
                    crate::leanh::lean_inc(v_fst_1981_);
                    crate::leanh::lean_dec(v_x_1980_);
                    v___x_1984_ = crate::leanh::lean_box(0);
                    v_isShared_1985_ = v_isSharedCheck_2004_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1986_ = l_Std_Http_Header_instReprName_repr___redArg(v_fst_1981_);
                v___x_1987_ = crate::leanh::lean_box(0);
                if v_isShared_1985_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1984_, 1);
                    crate::leanh::lean_ctor_set(v___x_1984_, 1, v___x_1987_);
                    crate::leanh::lean_ctor_set(v___x_1984_, 0, v___x_1986_);
                    v___x_1989_ = v___x_1984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_1987_);
                    v___x_1989_ = v_reuseFailAlloc_2003_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1990_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8(v_snd_1982_);
                v___x_1991_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1991_, 0, v___x_1990_);
                crate::leanh::lean_ctor_set(v___x_1991_, 1, v___x_1989_);
                v___x_1992_ = l_List_reverse___redArg(v___x_1991_);
                v___x_1993_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3;
                v___x_1994_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(v___x_1992_, v___x_1993_);
                v___x_1995_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3);
                v___x_1996_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4;
                v___x_1997_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1997_, 0, v___x_1996_);
                crate::leanh::lean_ctor_set(v___x_1997_, 1, v___x_1994_);
                v___x_1998_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5;
                v___x_1999_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1999_, 0, v___x_1997_);
                crate::leanh::lean_ctor_set(v___x_1999_, 1, v___x_1998_);
                v___x_2000_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2000_, 0, v___x_1995_);
                crate::leanh::lean_ctor_set(v___x_2000_, 1, v___x_1999_);
                v___x_2001_ = 0;
                v___x_2002_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2002_, 0, v___x_2000_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2002_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2001_,
                );
                return v___x_2002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10_spec__16(
    mut v_x_2005_: *mut crate::leanh::LeanObject,
    mut v_x_2006_: *mut crate::leanh::LeanObject,
    mut v_x_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2007_) == 0 {
                    crate::leanh::lean_dec(v_x_2005_);
                    return v_x_2006_;
                } else {
                    v_head_2008_ = crate::leanh::lean_ctor_get(v_x_2007_, 0);
                    v_tail_2009_ = crate::leanh::lean_ctor_get(v_x_2007_, 1);
                    v_isSharedCheck_2019_ = (!crate::leanh::lean_is_exclusive(v_x_2007_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_2011_ = v_x_2007_;
                        v_isShared_2012_ = v_isSharedCheck_2019_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2009_);
                        crate::leanh::lean_inc(v_head_2008_);
                        crate::leanh::lean_dec(v_x_2007_);
                        v___x_2011_ = crate::leanh::lean_box(0);
                        v_isShared_2012_ = v_isSharedCheck_2019_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2005_);
                if v_isShared_2012_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2011_, 5);
                    crate::leanh::lean_ctor_set(v___x_2011_, 1, v_x_2005_);
                    crate::leanh::lean_ctor_set(v___x_2011_, 0, v_x_2006_);
                    v___x_2014_ = v___x_2011_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_x_2006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_x_2005_);
                    v___x_2014_ = v_reuseFailAlloc_2018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2015_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_2008_);
                v___x_2016_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2016_, 0, v___x_2014_);
                crate::leanh::lean_ctor_set(v___x_2016_, 1, v___x_2015_);
                v_x_2006_ = v___x_2016_;
                v_x_2007_ = v_tail_2009_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10(
    mut v_x_2020_: *mut crate::leanh::LeanObject,
    mut v_x_2021_: *mut crate::leanh::LeanObject,
    mut v_x_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2022_) == 0 {
                    crate::leanh::lean_dec(v_x_2020_);
                    return v_x_2021_;
                } else {
                    v_head_2023_ = crate::leanh::lean_ctor_get(v_x_2022_, 0);
                    v_tail_2024_ = crate::leanh::lean_ctor_get(v_x_2022_, 1);
                    v_isSharedCheck_2034_ = (!crate::leanh::lean_is_exclusive(v_x_2022_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v___x_2026_ = v_x_2022_;
                        v_isShared_2027_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2024_);
                        crate::leanh::lean_inc(v_head_2023_);
                        crate::leanh::lean_dec(v_x_2022_);
                        v___x_2026_ = crate::leanh::lean_box(0);
                        v_isShared_2027_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2020_);
                if v_isShared_2027_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2026_, 5);
                    crate::leanh::lean_ctor_set(v___x_2026_, 1, v_x_2020_);
                    crate::leanh::lean_ctor_set(v___x_2026_, 0, v_x_2021_);
                    v___x_2029_ = v___x_2026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_x_2021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_x_2020_);
                    v___x_2029_ = v_reuseFailAlloc_2033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2030_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_2023_);
                v___x_2031_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2031_, 0, v___x_2029_);
                crate::leanh::lean_ctor_set(v___x_2031_, 1, v___x_2030_);
                v___x_2032_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10_spec__16(v_x_2020_, v___x_2031_, v_tail_2024_);
                return v___x_2032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6(
    mut v_x_2035_: *mut crate::leanh::LeanObject,
    mut v_x_2036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2035_) == 0 {
        let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2036_);
        v___x_2037_ = crate::leanh::lean_box(0);
        return v___x_2037_;
    } else {
        let mut v_tail_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2038_ = crate::leanh::lean_ctor_get(v_x_2035_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2038_) == 0 {
            let mut v_head_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_2036_);
            v_head_2039_ = crate::leanh::lean_ctor_get(v_x_2035_, 0);
            crate::leanh::lean_inc(v_head_2039_);
            crate::leanh::lean_dec_ref_known(v_x_2035_, 2);
            v___x_2040_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_2039_);
            return v___x_2040_;
        } else {
            let mut v_head_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2038_);
            v_head_2041_ = crate::leanh::lean_ctor_get(v_x_2035_, 0);
            crate::leanh::lean_inc(v_head_2041_);
            crate::leanh::lean_dec_ref_known(v_x_2035_, 2);
            v___x_2042_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_2041_);
            v___x_2043_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10(v_x_2036_, v___x_2042_, v_tail_2038_);
            return v___x_2043_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2048_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2;
    v___x_2049_ = lean_string_length(v___x_2048_);
    return v___x_2049_;
}
pub unsafe fn _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3_once), _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3);
    v___x_2051_ = lean_nat_to_int(v___x_2050_);
    return v___x_2051_;
}
pub unsafe fn l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(
    mut v_a_2054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_2054_) == 0 {
        let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2055_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1;
        return v___x_2055_;
    } else {
        let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: u8 = 0;
        let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2056_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3;
        v___x_2057_ = l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6(v_a_2054_, v___x_2056_);
        v___x_2058_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4_once), _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4);
        v___x_2059_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5;
        v___x_2060_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2060_, 0, v___x_2059_);
        crate::leanh::lean_ctor_set(v___x_2060_, 1, v___x_2057_);
        v___x_2061_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8;
        v___x_2062_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2062_, 0, v___x_2060_);
        crate::leanh::lean_ctor_set(v___x_2062_, 1, v___x_2061_);
        v___x_2063_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2063_, 0, v___x_2058_);
        crate::leanh::lean_ctor_set(v___x_2063_, 1, v___x_2062_);
        v___x_2064_ = 0;
        v___x_2065_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_2065_, 0, v___x_2063_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_2065_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_2064_,
        );
        return v___x_2065_;
    }
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(
    mut v_x_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2071_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: u8 = 0;
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2067_ = crate::leanh::lean_ctor_get(v_x_2066_, 0);
                v_snd_2068_ = crate::leanh::lean_ctor_get(v_x_2066_, 1);
                v_isSharedCheck_2090_ = (!crate::leanh::lean_is_exclusive(v_x_2066_)) as u8;
                if v_isSharedCheck_2090_ == 0 {
                    v___x_2070_ = v_x_2066_;
                    v_isShared_2071_ = v_isSharedCheck_2090_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2068_);
                    crate::leanh::lean_inc(v_fst_2067_);
                    crate::leanh::lean_dec(v_x_2066_);
                    v___x_2070_ = crate::leanh::lean_box(0);
                    v_isShared_2071_ = v_isSharedCheck_2090_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2072_ = l_Std_Http_Header_instReprName_repr___redArg(v_fst_2067_);
                v___x_2073_ = crate::leanh::lean_box(0);
                if v_isShared_2071_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2070_, 1);
                    crate::leanh::lean_ctor_set(v___x_2070_, 1, v___x_2073_);
                    crate::leanh::lean_ctor_set(v___x_2070_, 0, v___x_2072_);
                    v___x_2075_ = v___x_2070_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2073_);
                    v___x_2075_ = v_reuseFailAlloc_2089_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2076_ = l_Std_Http_Header_instReprValue_repr___redArg(v_snd_2068_);
                v___x_2077_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2077_, 0, v___x_2076_);
                crate::leanh::lean_ctor_set(v___x_2077_, 1, v___x_2075_);
                v___x_2078_ = l_List_reverse___redArg(v___x_2077_);
                v___x_2079_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3;
                v___x_2080_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(v___x_2078_, v___x_2079_);
                v___x_2081_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3);
                v___x_2082_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4;
                v___x_2083_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2083_, 0, v___x_2082_);
                crate::leanh::lean_ctor_set(v___x_2083_, 1, v___x_2080_);
                v___x_2084_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5;
                v___x_2085_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2083_);
                crate::leanh::lean_ctor_set(v___x_2085_, 1, v___x_2084_);
                v___x_2086_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2086_, 0, v___x_2081_);
                crate::leanh::lean_ctor_set(v___x_2086_, 1, v___x_2085_);
                v___x_2087_ = 0;
                v___x_2088_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_2086_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2088_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2087_,
                );
                return v___x_2088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__10(
    mut v_x_2091_: *mut crate::leanh::LeanObject,
    mut v_x_2092_: *mut crate::leanh::LeanObject,
    mut v_x_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2098_: u8 = 0;
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2093_) == 0 {
                    crate::leanh::lean_dec(v_x_2091_);
                    return v_x_2092_;
                } else {
                    v_head_2094_ = crate::leanh::lean_ctor_get(v_x_2093_, 0);
                    v_tail_2095_ = crate::leanh::lean_ctor_get(v_x_2093_, 1);
                    v_isSharedCheck_2105_ = (!crate::leanh::lean_is_exclusive(v_x_2093_)) as u8;
                    if v_isSharedCheck_2105_ == 0 {
                        v___x_2097_ = v_x_2093_;
                        v_isShared_2098_ = v_isSharedCheck_2105_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2095_);
                        crate::leanh::lean_inc(v_head_2094_);
                        crate::leanh::lean_dec(v_x_2093_);
                        v___x_2097_ = crate::leanh::lean_box(0);
                        v_isShared_2098_ = v_isSharedCheck_2105_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2091_);
                if v_isShared_2098_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2097_, 5);
                    crate::leanh::lean_ctor_set(v___x_2097_, 1, v_x_2091_);
                    crate::leanh::lean_ctor_set(v___x_2097_, 0, v_x_2092_);
                    v___x_2100_ = v___x_2097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2104_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_x_2092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_x_2091_);
                    v___x_2100_ = v_reuseFailAlloc_2104_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2101_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_2094_);
                v___x_2102_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_2100_);
                crate::leanh::lean_ctor_set(v___x_2102_, 1, v___x_2101_);
                v_x_2092_ = v___x_2102_;
                v_x_2093_ = v_tail_2095_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(
    mut v_x_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
    mut v_x_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2108_) == 0 {
                    crate::leanh::lean_dec(v_x_2106_);
                    return v_x_2107_;
                } else {
                    v_head_2109_ = crate::leanh::lean_ctor_get(v_x_2108_, 0);
                    v_tail_2110_ = crate::leanh::lean_ctor_get(v_x_2108_, 1);
                    v_isSharedCheck_2120_ = (!crate::leanh::lean_is_exclusive(v_x_2108_)) as u8;
                    if v_isSharedCheck_2120_ == 0 {
                        v___x_2112_ = v_x_2108_;
                        v_isShared_2113_ = v_isSharedCheck_2120_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2110_);
                        crate::leanh::lean_inc(v_head_2109_);
                        crate::leanh::lean_dec(v_x_2108_);
                        v___x_2112_ = crate::leanh::lean_box(0);
                        v_isShared_2113_ = v_isSharedCheck_2120_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2106_);
                if v_isShared_2113_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2112_, 5);
                    crate::leanh::lean_ctor_set(v___x_2112_, 1, v_x_2106_);
                    crate::leanh::lean_ctor_set(v___x_2112_, 0, v_x_2107_);
                    v___x_2115_ = v___x_2112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_x_2107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_x_2106_);
                    v___x_2115_ = v_reuseFailAlloc_2119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2116_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_2109_);
                v___x_2117_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2117_, 0, v___x_2115_);
                crate::leanh::lean_ctor_set(v___x_2117_, 1, v___x_2116_);
                v___x_2118_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__10(v_x_2106_, v___x_2117_, v_tail_2110_);
                return v___x_2118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(
    mut v_x_2121_: *mut crate::leanh::LeanObject,
    mut v_x_2122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2121_) == 0 {
        let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2122_);
        v___x_2123_ = crate::leanh::lean_box(0);
        return v___x_2123_;
    } else {
        let mut v_tail_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2124_ = crate::leanh::lean_ctor_get(v_x_2121_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2124_) == 0 {
            let mut v_head_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_2122_);
            v_head_2125_ = crate::leanh::lean_ctor_get(v_x_2121_, 0);
            crate::leanh::lean_inc(v_head_2125_);
            crate::leanh::lean_dec_ref_known(v_x_2121_, 2);
            v___x_2126_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_2125_);
            return v___x_2126_;
        } else {
            let mut v_head_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2124_);
            v_head_2127_ = crate::leanh::lean_ctor_get(v_x_2121_, 0);
            crate::leanh::lean_inc(v_head_2127_);
            crate::leanh::lean_dec_ref_known(v_x_2121_, 2);
            v___x_2128_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_2127_);
            v___x_2129_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(v_x_2122_, v___x_2128_, v_tail_2124_);
            return v___x_2129_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(
    mut v_xs_2130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: u8 = 0;
    v___x_2131_ = lean_array_get_size(v_xs_2130_);
    v___x_2132_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2133_ = lean_nat_dec_eq(v___x_2131_, v___x_2132_);
    if v___x_2133_ == 0 {
        let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2134_ = lean_array_to_list(v_xs_2130_);
        v___x_2135_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3;
        v___x_2136_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(v___x_2134_, v___x_2135_);
        v___x_2137_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6_once), _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6);
        v___x_2138_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7;
        v___x_2139_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2139_, 0, v___x_2138_);
        crate::leanh::lean_ctor_set(v___x_2139_, 1, v___x_2136_);
        v___x_2140_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8;
        v___x_2141_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2141_, 0, v___x_2139_);
        crate::leanh::lean_ctor_set(v___x_2141_, 1, v___x_2140_);
        v___x_2142_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2142_, 0, v___x_2137_);
        crate::leanh::lean_ctor_set(v___x_2142_, 1, v___x_2141_);
        v___x_2143_ = l_Std_Format_fill(v___x_2142_);
        return v___x_2143_;
    } else {
        let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_2130_);
        v___x_2144_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10;
        return v___x_2144_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(
    mut v_x_2145_: *mut crate::leanh::LeanObject,
    mut v_x_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2146_) == 0 {
        crate::leanh::lean_inc(v_x_2145_);
        return v_x_2145_;
    } else {
        let mut v_key_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_2147_ = crate::leanh::lean_ctor_get(v_x_2146_, 0);
        v_value_2148_ = crate::leanh::lean_ctor_get(v_x_2146_, 1);
        v_tail_2149_ = crate::leanh::lean_ctor_get(v_x_2146_, 2);
        v___x_2150_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_x_2145_, v_tail_2149_);
        crate::leanh::lean_inc(v_value_2148_);
        crate::leanh::lean_inc(v_key_2147_);
        v___x_2151_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2151_, 0, v_key_2147_);
        crate::leanh::lean_ctor_set(v___x_2151_, 1, v_value_2148_);
        v___x_2152_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2152_, 0, v___x_2151_);
        crate::leanh::lean_ctor_set(v___x_2152_, 1, v___x_2150_);
        return v___x_2152_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___boxed(
    mut v_x_2153_: *mut crate::leanh::LeanObject,
    mut v_x_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2155_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_x_2153_, v_x_2154_);
    crate::leanh::lean_dec(v_x_2154_);
    crate::leanh::lean_dec(v_x_2153_);
    return v_res_2155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(
    mut v_as_2156_: *mut crate::leanh::LeanObject,
    mut v_i_2157_: usize,
    mut v_stop_2158_: usize,
    mut v_b_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: usize = 0;
    let mut v___x_2162_: usize = 0;
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2160_ = lean_usize_dec_eq(v_i_2157_, v_stop_2158_);
                if v___x_2160_ == 0 {
                    v___x_2161_ = 1usize;
                    v___x_2162_ = lean_usize_sub(v_i_2157_, v___x_2161_);
                    v___x_2163_ = lean_array_uget_borrowed(v_as_2156_, v___x_2162_);
                    v___x_2164_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_b_2159_, v___x_2163_);
                    crate::leanh::lean_dec(v_b_2159_);
                    v_i_2157_ = v___x_2162_;
                    v_b_2159_ = v___x_2164_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2159_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3___boxed(
    mut v_as_2166_: *mut crate::leanh::LeanObject,
    mut v_i_2167_: *mut crate::leanh::LeanObject,
    mut v_stop_2168_: *mut crate::leanh::LeanObject,
    mut v_b_2169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2170_: usize = 0;
    let mut v_stop_boxed_2171_: usize = 0;
    let mut v_res_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2170_ = crate::leanh::lean_unbox_usize(v_i_2167_);
    crate::leanh::lean_dec(v_i_2167_);
    v_stop_boxed_2171_ = crate::leanh::lean_unbox_usize(v_stop_2168_);
    crate::leanh::lean_dec(v_stop_2168_);
    v_res_2172_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(v_as_2166_, v_i_boxed_2170_, v_stop_boxed_2171_, v_b_2169_);
    crate::leanh::lean_dec_ref(v_as_2166_);
    return v_res_2172_;
}
pub unsafe fn _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2186_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2187_ = lean_nat_to_int(v___x_2186_);
    return v___x_2187_;
}
pub unsafe fn _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2201_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6;
    v___x_2202_ = lean_string_length(v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17), core::ptr::addr_of_mut!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17_once), _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17);
    v___x_2204_ = lean_nat_to_int(v___x_2203_);
    return v___x_2204_;
}
pub unsafe fn l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(
    mut v_x_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_indexes_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2214_: u8 = 0;
    let mut v_buckets_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2263_: usize = 0;
    let mut v___x_2264_: usize = 0;
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut v_unused_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_indexes_2210_ = crate::leanh::lean_ctor_get(v_x_2209_, 1);
                v_entries_2211_ = crate::leanh::lean_ctor_get(v_x_2209_, 0);
                v_isSharedCheck_2270_ = (!crate::leanh::lean_is_exclusive(v_x_2209_)) as u8;
                if v_isSharedCheck_2270_ == 0 {
                    v___x_2213_ = v_x_2209_;
                    v_isShared_2214_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_2210_);
                    crate::leanh::lean_inc(v_entries_2211_);
                    crate::leanh::lean_dec(v_x_2209_);
                    v___x_2213_ = crate::leanh::lean_box(0);
                    v_isShared_2214_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_buckets_2215_ = crate::leanh::lean_ctor_get(v_indexes_2210_, 1);
                v_isSharedCheck_2268_ = (!crate::leanh::lean_is_exclusive(v_indexes_2210_)) as u8;
                if v_isSharedCheck_2268_ == 0 {
                    v_unused_2269_ = crate::leanh::lean_ctor_get(v_indexes_2210_, 0);
                    crate::leanh::lean_dec(v_unused_2269_);
                    v___x_2217_ = v_indexes_2210_;
                    v_isShared_2218_ = v_isSharedCheck_2268_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2215_);
                    crate::leanh::lean_dec(v_indexes_2210_);
                    v___x_2217_ = crate::leanh::lean_box(0);
                    v_isShared_2218_ = v_isSharedCheck_2268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2219_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4;
                v___x_2220_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5;
                v___x_2221_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once), _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7);
                v___x_2222_ = l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(v_entries_2211_);
                if v_isShared_2218_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2217_, 4);
                    crate::leanh::lean_ctor_set(v___x_2217_, 1, v___x_2222_);
                    crate::leanh::lean_ctor_set(v___x_2217_, 0, v___x_2221_);
                    v___x_2224_ = v___x_2217_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2267_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2222_);
                    v___x_2224_ = v_reuseFailAlloc_2267_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2225_ = 0;
                v___x_2226_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2226_, 0, v___x_2224_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2226_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2225_,
                );
                if v_isShared_2214_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2213_, 5);
                    crate::leanh::lean_ctor_set(v___x_2213_, 1, v___x_2226_);
                    crate::leanh::lean_ctor_set(v___x_2213_, 0, v___x_2220_);
                    v___x_2228_ = v___x_2213_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2266_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2226_);
                    v___x_2228_ = v_reuseFailAlloc_2266_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2229_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2;
                v___x_2230_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2230_, 0, v___x_2228_);
                crate::leanh::lean_ctor_set(v___x_2230_, 1, v___x_2229_);
                v___x_2231_ = crate::leanh::lean_box(1);
                v___x_2232_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2232_, 0, v___x_2230_);
                crate::leanh::lean_ctor_set(v___x_2232_, 1, v___x_2231_);
                v___x_2233_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9;
                v___x_2234_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2234_, 0, v___x_2232_);
                crate::leanh::lean_ctor_set(v___x_2234_, 1, v___x_2233_);
                v___x_2235_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2235_, 0, v___x_2234_);
                crate::leanh::lean_ctor_set(v___x_2235_, 1, v___x_2219_);
                v___x_2236_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2237_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11;
                v___x_2260_ = crate::leanh::lean_box(0);
                v___x_2261_ = lean_array_get_size(v_buckets_2215_);
                v___x_2262_ = lean_nat_dec_lt(v___x_2236_, v___x_2261_);
                if v___x_2262_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_2215_);
                    v___y_2239_ = v___x_2260_;
                    state = 5;
                    continue;
                } else {
                    v___x_2263_ = lean_usize_of_nat(v___x_2261_);
                    v___x_2264_ = 0usize;
                    v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(v_buckets_2215_, v___x_2263_, v___x_2264_, v___x_2260_);
                    crate::leanh::lean_dec_ref(v_buckets_2215_);
                    v___y_2239_ = v___x_2265_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2240_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(v___y_2239_);
                v___x_2241_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2241_, 0, v___x_2237_);
                crate::leanh::lean_ctor_set(v___x_2241_, 1, v___x_2240_);
                v___x_2242_ = l_Repr_addAppParen(v___x_2241_, v___x_2236_);
                v___x_2243_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2243_, 0, v___x_2221_);
                crate::leanh::lean_ctor_set(v___x_2243_, 1, v___x_2242_);
                v___x_2244_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2244_, 0, v___x_2243_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2244_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2225_,
                );
                v___x_2245_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2235_);
                crate::leanh::lean_ctor_set(v___x_2245_, 1, v___x_2244_);
                v___x_2246_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2246_, 0, v___x_2245_);
                crate::leanh::lean_ctor_set(v___x_2246_, 1, v___x_2229_);
                v___x_2247_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2247_, 0, v___x_2246_);
                crate::leanh::lean_ctor_set(v___x_2247_, 1, v___x_2231_);
                v___x_2248_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13;
                v___x_2249_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2249_, 0, v___x_2247_);
                crate::leanh::lean_ctor_set(v___x_2249_, 1, v___x_2248_);
                v___x_2250_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2250_, 0, v___x_2249_);
                crate::leanh::lean_ctor_set(v___x_2250_, 1, v___x_2219_);
                v___x_2251_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15;
                v___x_2252_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2252_, 0, v___x_2250_);
                crate::leanh::lean_ctor_set(v___x_2252_, 1, v___x_2251_);
                v___x_2253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18), core::ptr::addr_of_mut!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once), _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
                v___x_2254_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19;
                v___x_2255_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2255_, 0, v___x_2254_);
                crate::leanh::lean_ctor_set(v___x_2255_, 1, v___x_2252_);
                v___x_2256_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20;
                v___x_2257_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2255_);
                crate::leanh::lean_ctor_set(v___x_2257_, 1, v___x_2256_);
                v___x_2258_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2258_, 0, v___x_2253_);
                crate::leanh::lean_ctor_set(v___x_2258_, 1, v___x_2257_);
                v___x_2259_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2259_, 0, v___x_2258_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2259_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2225_,
                );
                return v___x_2259_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_2281_ = lean_nat_to_int(v___x_2280_);
    return v___x_2281_;
}
pub unsafe fn l_Std_Http_instReprHeaders_repr___redArg(
    mut v_x_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2283_ = l_Std_Http_instReprHeaders_repr___redArg___closed__3;
    v___x_2284_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instReprHeaders_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Std_Http_instReprHeaders_repr___redArg___closed__4_once),
        _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4,
    );
    v___x_2285_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_2282_);
    v___x_2286_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2286_, 0, v___x_2284_);
    crate::leanh::lean_ctor_set(v___x_2286_, 1, v___x_2285_);
    v___x_2287_ = 0;
    v___x_2288_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2288_, 0, v___x_2286_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2288_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2287_,
    );
    v___x_2289_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2283_);
    crate::leanh::lean_ctor_set(v___x_2289_, 1, v___x_2288_);
    v___x_2290_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18), core::ptr::addr_of_mut!(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once), _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
    v___x_2291_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19;
    v___x_2292_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2292_, 0, v___x_2291_);
    crate::leanh::lean_ctor_set(v___x_2292_, 1, v___x_2289_);
    v___x_2293_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20;
    v___x_2294_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2294_, 0, v___x_2292_);
    crate::leanh::lean_ctor_set(v___x_2294_, 1, v___x_2293_);
    v___x_2295_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2295_, 0, v___x_2290_);
    crate::leanh::lean_ctor_set(v___x_2295_, 1, v___x_2294_);
    v___x_2296_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2296_, 0, v___x_2295_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2296_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2287_,
    );
    return v___x_2296_;
}
pub unsafe fn l_Std_Http_instReprHeaders_repr(
    mut v_x_2297_: *mut crate::leanh::LeanObject,
    mut v_prec_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_Std_Http_instReprHeaders_repr___redArg(v_x_2297_);
    return v___x_2299_;
}
pub unsafe fn l_Std_Http_instReprHeaders_repr___boxed(
    mut v_x_2300_: *mut crate::leanh::LeanObject,
    mut v_prec_2301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2302_ = l_Std_Http_instReprHeaders_repr(v_x_2300_, v_prec_2301_);
    crate::leanh::lean_dec(v_prec_2301_);
    return v_res_2302_;
}
pub unsafe fn l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(
    mut v_x_2303_: *mut crate::leanh::LeanObject,
    mut v_prec_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_2303_);
    return v___x_2305_;
}
pub unsafe fn l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(
    mut v_x_2306_: *mut crate::leanh::LeanObject,
    mut v_prec_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2308_ =
        l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(
            v_x_2306_,
            v_prec_2307_,
        );
    crate::leanh::lean_dec(v_prec_2307_);
    return v_res_2308_;
}
pub unsafe fn l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(
    mut v_a_2309_: *mut crate::leanh::LeanObject,
    mut v_n_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2311_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(v_a_2309_);
    return v___x_2311_;
}
pub unsafe fn l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___boxed(
    mut v_a_2312_: *mut crate::leanh::LeanObject,
    mut v_n_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2314_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(v_a_2312_, v_n_2313_);
    crate::leanh::lean_dec(v_n_2313_);
    return v_res_2314_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(
    mut v_x_2315_: *mut crate::leanh::LeanObject,
    mut v_x_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2317_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_x_2315_);
    return v___x_2317_;
}
pub unsafe fn l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(
    mut v_x_2318_: *mut crate::leanh::LeanObject,
    mut v_x_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(v_x_2318_, v_x_2319_);
    crate::leanh::lean_dec(v_x_2319_);
    return v_res_2320_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(
    mut v_x_2321_: *mut crate::leanh::LeanObject,
    mut v_x_2322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2323_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_x_2321_);
    return v___x_2323_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___boxed(
    mut v_x_2324_: *mut crate::leanh::LeanObject,
    mut v_x_2325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2326_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(v_x_2324_, v_x_2325_);
    crate::leanh::lean_dec(v_x_2325_);
    return v_res_2326_;
}
pub unsafe fn _init_l_Std_Http_instMembershipNameHeaders() -> *mut crate::leanh::LeanObject {
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2329_ = crate::leanh::lean_box(0);
    return v___x_2329_;
}
pub unsafe fn l_Std_Http_instDecidableMemNameHeaders(
    mut v_name_2332_: *mut crate::leanh::LeanObject,
    mut v_h_2333_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    v___f_2334_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2335_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    v___x_2336_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_2334_,
        v___f_2335_,
        v_name_2332_,
        v_h_2333_,
    );
    return v___x_2336_;
}
pub unsafe fn l_Std_Http_instDecidableMemNameHeaders___boxed(
    mut v_name_2337_: *mut crate::leanh::LeanObject,
    mut v_h_2338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2339_: u8 = 0;
    let mut v_r_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2339_ = l_Std_Http_instDecidableMemNameHeaders(v_name_2337_, v_h_2338_);
    crate::leanh::lean_dec_ref(v_h_2338_);
    v_r_2340_ = crate::leanh::lean_box((v_res_2339_) as usize);
    return v_r_2340_;
}
pub unsafe fn l_Std_Http_Headers_get___redArg(
    mut v_headers_2341_: *mut crate::leanh::LeanObject,
    mut v_name_2342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_entries_2343_ = crate::leanh::lean_ctor_get(v_headers_2341_, 0);
    v_indexes_2344_ = crate::leanh::lean_ctor_get(v_headers_2341_, 1);
    v___f_2345_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2346_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    v___x_2347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v___f_2345_,
        v___f_2346_,
        v_indexes_2344_,
        v_name_2342_,
    );
    v___x_2348_ = crate::leanh::lean_unsigned_to_nat(0);
    v_entry_2349_ = lean_array_fget(v___x_2347_, v___x_2348_);
    crate::leanh::lean_dec(v___x_2347_);
    v___x_2350_ = lean_array_fget_borrowed(v_entries_2343_, v_entry_2349_);
    crate::leanh::lean_dec(v_entry_2349_);
    v_snd_2351_ = crate::leanh::lean_ctor_get(v___x_2350_, 1);
    crate::leanh::lean_inc(v_snd_2351_);
    return v_snd_2351_;
}
pub unsafe fn l_Std_Http_Headers_get___redArg___boxed(
    mut v_headers_2352_: *mut crate::leanh::LeanObject,
    mut v_name_2353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2354_ = l_Std_Http_Headers_get___redArg(v_headers_2352_, v_name_2353_);
    crate::leanh::lean_dec_ref(v_headers_2352_);
    return v_res_2354_;
}
pub unsafe fn l_Std_Http_Headers_get(
    mut v_headers_2355_: *mut crate::leanh::LeanObject,
    mut v_name_2356_: *mut crate::leanh::LeanObject,
    mut v_h_2357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_entries_2358_ = crate::leanh::lean_ctor_get(v_headers_2355_, 0);
    v_indexes_2359_ = crate::leanh::lean_ctor_get(v_headers_2355_, 1);
    v___f_2360_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2361_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    v___x_2362_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v___f_2360_,
        v___f_2361_,
        v_indexes_2359_,
        v_name_2356_,
    );
    v___x_2363_ = crate::leanh::lean_unsigned_to_nat(0);
    v_entry_2364_ = lean_array_fget(v___x_2362_, v___x_2363_);
    crate::leanh::lean_dec(v___x_2362_);
    v___x_2365_ = lean_array_fget_borrowed(v_entries_2358_, v_entry_2364_);
    crate::leanh::lean_dec(v_entry_2364_);
    v_snd_2366_ = crate::leanh::lean_ctor_get(v___x_2365_, 1);
    crate::leanh::lean_inc(v_snd_2366_);
    return v_snd_2366_;
}
pub unsafe fn l_Std_Http_Headers_get___boxed(
    mut v_headers_2367_: *mut crate::leanh::LeanObject,
    mut v_name_2368_: *mut crate::leanh::LeanObject,
    mut v_h_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2370_ = l_Std_Http_Headers_get(v_headers_2367_, v_name_2368_, v_h_2369_);
    crate::leanh::lean_dec_ref(v_headers_2367_);
    return v_res_2370_;
}
pub unsafe fn l_Std_Http_Headers_getAll___redArg___lam__0(
    mut v___x_2371_: *mut crate::leanh::LeanObject,
    mut v_entries_2372_: *mut crate::leanh::LeanObject,
    mut v_x1_2373_: *mut crate::leanh::LeanObject,
    mut v_x2_2374_: *mut crate::leanh::LeanObject,
    mut v_x3_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = lean_array_fget_borrowed(v___x_2371_, v_x1_2373_);
    v___x_2377_ = lean_array_fget_borrowed(v_entries_2372_, v___x_2376_);
    v_snd_2378_ = crate::leanh::lean_ctor_get(v___x_2377_, 1);
    crate::leanh::lean_inc(v_snd_2378_);
    return v_snd_2378_;
}
pub unsafe fn l_Std_Http_Headers_getAll___redArg___lam__0___boxed(
    mut v___x_2379_: *mut crate::leanh::LeanObject,
    mut v_entries_2380_: *mut crate::leanh::LeanObject,
    mut v_x1_2381_: *mut crate::leanh::LeanObject,
    mut v_x2_2382_: *mut crate::leanh::LeanObject,
    mut v_x3_2383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2384_ = l_Std_Http_Headers_getAll___redArg___lam__0(
        v___x_2379_,
        v_entries_2380_,
        v_x1_2381_,
        v_x2_2382_,
        v_x3_2383_,
    );
    crate::leanh::lean_dec(v_x2_2382_);
    crate::leanh::lean_dec(v_x1_2381_);
    crate::leanh::lean_dec_ref(v_entries_2380_);
    crate::leanh::lean_dec_ref(v___x_2379_);
    return v_res_2384_;
}
pub unsafe fn l_Std_Http_Headers_getAll___redArg(
    mut v_headers_2404_: *mut crate::leanh::LeanObject,
    mut v_name_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_entries_2406_ = crate::leanh::lean_ctor_get(v_headers_2404_, 0);
    crate::leanh::lean_inc_ref(v_entries_2406_);
    v_indexes_2407_ = crate::leanh::lean_ctor_get(v_headers_2404_, 1);
    crate::leanh::lean_inc_ref(v_indexes_2407_);
    crate::leanh::lean_dec_ref(v_headers_2404_);
    v___f_2408_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2409_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    v___x_2410_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v___f_2408_,
        v___f_2409_,
        v_indexes_2407_,
        v_name_2405_,
    );
    crate::leanh::lean_dec_ref(v_indexes_2407_);
    crate::leanh::lean_inc(v___x_2410_);
    v___f_2411_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Headers_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2411_, 0, v___x_2410_);
    crate::leanh::lean_closure_set(v___f_2411_, 1, v_entries_2406_);
    v___x_2412_ = l_Std_Http_Headers_getAll___redArg___closed__9;
    v___x_2413_ = lean_array_get_size(v___x_2410_);
    v___x_2414_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2415_ = lean_mk_empty_array_with_capacity(v___x_2413_);
    v_entries_2416_ = l_Array_mapFinIdxM_map___redArg(
        v___x_2412_,
        v___x_2410_,
        v___f_2411_,
        v___x_2413_,
        v___x_2414_,
        v___x_2415_,
    );
    return v_entries_2416_;
}
pub unsafe fn l_Std_Http_Headers_getAll(
    mut v_headers_2417_: *mut crate::leanh::LeanObject,
    mut v_name_2418_: *mut crate::leanh::LeanObject,
    mut v_h_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_entries_2420_ = crate::leanh::lean_ctor_get(v_headers_2417_, 0);
    crate::leanh::lean_inc_ref(v_entries_2420_);
    v_indexes_2421_ = crate::leanh::lean_ctor_get(v_headers_2417_, 1);
    crate::leanh::lean_inc_ref(v_indexes_2421_);
    crate::leanh::lean_dec_ref(v_headers_2417_);
    v___f_2422_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2423_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    v___x_2424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
        v___f_2422_,
        v___f_2423_,
        v_indexes_2421_,
        v_name_2418_,
    );
    crate::leanh::lean_dec_ref(v_indexes_2421_);
    crate::leanh::lean_inc(v___x_2424_);
    v___f_2425_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Headers_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2425_, 0, v___x_2424_);
    crate::leanh::lean_closure_set(v___f_2425_, 1, v_entries_2420_);
    v___x_2426_ = l_Std_Http_Headers_getAll___redArg___closed__9;
    v___x_2427_ = lean_array_get_size(v___x_2424_);
    v___x_2428_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2429_ = lean_mk_empty_array_with_capacity(v___x_2427_);
    v_entries_2430_ = l_Array_mapFinIdxM_map___redArg(
        v___x_2426_,
        v___x_2424_,
        v___f_2425_,
        v___x_2427_,
        v___x_2428_,
        v___x_2429_,
    );
    return v_entries_2430_;
}
pub unsafe fn l_Std_Http_Headers_getAll_x3f(
    mut v_headers_2431_: *mut crate::leanh::LeanObject,
    mut v_name_2432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u8 = 0;
    v___f_2433_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2434_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    crate::leanh::lean_inc_ref(v_name_2432_);
    v___x_2435_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_2433_,
        v___f_2434_,
        v_name_2432_,
        v_headers_2431_,
    );
    if v___x_2435_ == 0 {
        let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_name_2432_);
        crate::leanh::lean_dec_ref(v_headers_2431_);
        v___x_2436_ = crate::leanh::lean_box(0);
        return v___x_2436_;
    } else {
        let mut v_entries_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_entries_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_entries_2437_ = crate::leanh::lean_ctor_get(v_headers_2431_, 0);
        crate::leanh::lean_inc_ref(v_entries_2437_);
        v_indexes_2438_ = crate::leanh::lean_ctor_get(v_headers_2431_, 1);
        crate::leanh::lean_inc_ref(v_indexes_2438_);
        crate::leanh::lean_dec_ref(v_headers_2431_);
        v___x_2439_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v___f_2433_,
            v___f_2434_,
            v_indexes_2438_,
            v_name_2432_,
        );
        crate::leanh::lean_dec_ref(v_indexes_2438_);
        crate::leanh::lean_inc(v___x_2439_);
        v___f_2440_ = crate::leanh::lean_alloc_closure(
            l_Std_Http_Headers_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2440_, 0, v___x_2439_);
        crate::leanh::lean_closure_set(v___f_2440_, 1, v_entries_2437_);
        v___x_2441_ = l_Std_Http_Headers_getAll___redArg___closed__9;
        v___x_2442_ = lean_array_get_size(v___x_2439_);
        v___x_2443_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2444_ = lean_mk_empty_array_with_capacity(v___x_2442_);
        v_entries_2445_ = l_Array_mapFinIdxM_map___redArg(
            v___x_2441_,
            v___x_2439_,
            v___f_2440_,
            v___x_2442_,
            v___x_2443_,
            v___x_2444_,
        );
        v___x_2446_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2446_, 0, v_entries_2445_);
        return v___x_2446_;
    }
}
pub unsafe fn l_Std_Http_Headers_get_x3f(
    mut v_headers_2447_: *mut crate::leanh::LeanObject,
    mut v_name_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: u8 = 0;
    v___f_2449_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2450_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    crate::leanh::lean_inc_ref(v_name_2448_);
    v___x_2451_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_2449_,
        v___f_2450_,
        v_name_2448_,
        v_headers_2447_,
    );
    if v___x_2451_ == 0 {
        let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_name_2448_);
        v___x_2452_ = crate::leanh::lean_box(0);
        return v___x_2452_;
    } else {
        let mut v_entries_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_entry_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_entries_2453_ = crate::leanh::lean_ctor_get(v_headers_2447_, 0);
        v_indexes_2454_ = crate::leanh::lean_ctor_get(v_headers_2447_, 1);
        v___x_2455_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v___f_2449_,
            v___f_2450_,
            v_indexes_2454_,
            v_name_2448_,
        );
        v___x_2456_ = crate::leanh::lean_unsigned_to_nat(0);
        v_entry_2457_ = lean_array_fget(v___x_2455_, v___x_2456_);
        crate::leanh::lean_dec(v___x_2455_);
        v___x_2458_ = lean_array_fget_borrowed(v_entries_2453_, v_entry_2457_);
        crate::leanh::lean_dec(v_entry_2457_);
        v_snd_2459_ = crate::leanh::lean_ctor_get(v___x_2458_, 1);
        crate::leanh::lean_inc(v_snd_2459_);
        v___x_2460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2460_, 0, v_snd_2459_);
        return v___x_2460_;
    }
}
pub unsafe fn l_Std_Http_Headers_get_x3f___boxed(
    mut v_headers_2461_: *mut crate::leanh::LeanObject,
    mut v_name_2462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2463_ = l_Std_Http_Headers_get_x3f(v_headers_2461_, v_name_2462_);
    crate::leanh::lean_dec_ref(v_headers_2461_);
    return v_res_2463_;
}
pub unsafe fn l_Std_Http_Headers_hasEntry___lam__1(
    mut v_value_2464_: *mut crate::leanh::LeanObject,
    mut v___x_2465_: *mut crate::leanh::LeanObject,
    mut v___x_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_x_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2470_: u8 = 0;
    v___x_2470_ = l_Std_Http_Header_instBEqValue_beq(v_a_2467_, v_value_2464_);
    if v___x_2470_ == 0 {
        let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_a_2467_);
        v___x_2471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2471_, 0, v___x_2465_);
        return v___x_2471_;
    } else {
        let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_2465_);
        v___x_2472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2472_, 0, v_a_2467_);
        v___x_2473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2473_, 0, v___x_2472_);
        v___x_2474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2474_, 0, v___x_2473_);
        crate::leanh::lean_ctor_set(v___x_2474_, 1, v___x_2466_);
        v___x_2475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2475_, 0, v___x_2474_);
        return v___x_2475_;
    }
}
pub unsafe fn l_Std_Http_Headers_hasEntry___lam__1___boxed(
    mut v_value_2476_: *mut crate::leanh::LeanObject,
    mut v___x_2477_: *mut crate::leanh::LeanObject,
    mut v___x_2478_: *mut crate::leanh::LeanObject,
    mut v_a_2479_: *mut crate::leanh::LeanObject,
    mut v_x_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2482_ = l_Std_Http_Headers_hasEntry___lam__1(
        v_value_2476_,
        v___x_2477_,
        v___x_2478_,
        v_a_2479_,
        v_x_2480_,
        v___y_2481_,
    );
    crate::leanh::lean_dec_ref(v___y_2481_);
    crate::leanh::lean_dec_ref(v_value_2476_);
    return v_res_2482_;
}
pub unsafe fn l_Std_Http_Headers_hasEntry(
    mut v_headers_2486_: *mut crate::leanh::LeanObject,
    mut v_name_2487_: *mut crate::leanh::LeanObject,
    mut v_value_2488_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    v___f_2489_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2490_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    crate::leanh::lean_inc_ref(v_name_2487_);
    v___x_2491_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_2489_,
        v___f_2490_,
        v_name_2487_,
        v_headers_2486_,
    );
    if v___x_2491_ == 0 {
        crate::leanh::lean_dec_ref(v_value_2488_);
        crate::leanh::lean_dec_ref(v_name_2487_);
        crate::leanh::lean_dec_ref(v_headers_2486_);
        return v___x_2491_;
    } else {
        let mut v_entries_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_entries_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2504_: usize = 0;
        let mut v___x_2505_: usize = 0;
        let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_entries_2492_ = crate::leanh::lean_ctor_get(v_headers_2486_, 0);
        crate::leanh::lean_inc_ref(v_entries_2492_);
        v_indexes_2493_ = crate::leanh::lean_ctor_get(v_headers_2486_, 1);
        crate::leanh::lean_inc_ref(v_indexes_2493_);
        crate::leanh::lean_dec_ref(v_headers_2486_);
        v___x_2494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v___f_2489_,
            v___f_2490_,
            v_indexes_2493_,
            v_name_2487_,
        );
        crate::leanh::lean_dec_ref(v_indexes_2493_);
        crate::leanh::lean_inc(v___x_2494_);
        v___f_2495_ = crate::leanh::lean_alloc_closure(
            l_Std_Http_Headers_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2495_, 0, v___x_2494_);
        crate::leanh::lean_closure_set(v___f_2495_, 1, v_entries_2492_);
        v___x_2496_ = l_Std_Http_Headers_getAll___redArg___closed__9;
        v___x_2497_ = lean_array_get_size(v___x_2494_);
        v___x_2498_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2499_ = lean_mk_empty_array_with_capacity(v___x_2497_);
        v_entries_2500_ = l_Array_mapFinIdxM_map___redArg(
            v___x_2496_,
            v___x_2494_,
            v___f_2495_,
            v___x_2497_,
            v___x_2498_,
            v___x_2499_,
        );
        v___x_2501_ = crate::leanh::lean_box(0);
        v___x_2502_ = l_Std_Http_Headers_hasEntry___closed__0;
        v___f_2503_ = crate::leanh::lean_alloc_closure(
            l_Std_Http_Headers_hasEntry___lam__1___boxed as *mut core::ffi::c_void,
            6,
            3,
        );
        crate::leanh::lean_closure_set(v___f_2503_, 0, v_value_2488_);
        crate::leanh::lean_closure_set(v___f_2503_, 1, v___x_2502_);
        crate::leanh::lean_closure_set(v___f_2503_, 2, v___x_2501_);
        v_sz_2504_ = lean_array_size(v_entries_2500_);
        v___x_2505_ = 0usize;
        v___x_2506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2496_,
            v_entries_2500_,
            v___f_2503_,
            v_sz_2504_,
            v___x_2505_,
            v___x_2502_,
        );
        v_fst_2507_ = crate::leanh::lean_ctor_get(v___x_2506_, 0);
        crate::leanh::lean_inc(v_fst_2507_);
        crate::leanh::lean_dec(v___x_2506_);
        if crate::leanh::lean_obj_tag(v_fst_2507_) == 0 {
            let mut v___x_2508_: u8 = 0;
            v___x_2508_ = 0;
            return v___x_2508_;
        } else {
            let mut v_val_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_2509_ = crate::leanh::lean_ctor_get(v_fst_2507_, 0);
            crate::leanh::lean_inc(v_val_2509_);
            crate::leanh::lean_dec_ref_known(v_fst_2507_, 1);
            if crate::leanh::lean_obj_tag(v_val_2509_) == 0 {
                let mut v___x_2510_: u8 = 0;
                v___x_2510_ = 0;
                return v___x_2510_;
            } else {
                crate::leanh::lean_dec_ref_known(v_val_2509_, 1);
                return v___x_2491_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_Headers_hasEntry___boxed(
    mut v_headers_2511_: *mut crate::leanh::LeanObject,
    mut v_name_2512_: *mut crate::leanh::LeanObject,
    mut v_value_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2514_: u8 = 0;
    let mut v_r_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2514_ = l_Std_Http_Headers_hasEntry(v_headers_2511_, v_name_2512_, v_value_2513_);
    v_r_2515_ = crate::leanh::lean_box((v_res_2514_) as usize);
    return v_r_2515_;
}
pub unsafe fn l_Std_Http_Headers_getLast_x3f(
    mut v_headers_2516_: *mut crate::leanh::LeanObject,
    mut v_name_2517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: u8 = 0;
    v___f_2518_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2519_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    crate::leanh::lean_inc_ref(v_name_2517_);
    v___x_2520_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_2518_,
        v___f_2519_,
        v_name_2517_,
        v_headers_2516_,
    );
    if v___x_2520_ == 0 {
        let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_name_2517_);
        crate::leanh::lean_dec_ref(v_headers_2516_);
        v___x_2521_ = crate::leanh::lean_box(0);
        return v___x_2521_;
    } else {
        let mut v_entries_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_entries_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2534_: u8 = 0;
        v_entries_2522_ = crate::leanh::lean_ctor_get(v_headers_2516_, 0);
        crate::leanh::lean_inc_ref(v_entries_2522_);
        v_indexes_2523_ = crate::leanh::lean_ctor_get(v_headers_2516_, 1);
        crate::leanh::lean_inc_ref(v_indexes_2523_);
        crate::leanh::lean_dec_ref(v_headers_2516_);
        v___x_2524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v___f_2518_,
            v___f_2519_,
            v_indexes_2523_,
            v_name_2517_,
        );
        crate::leanh::lean_dec_ref(v_indexes_2523_);
        crate::leanh::lean_inc(v___x_2524_);
        v___f_2525_ = crate::leanh::lean_alloc_closure(
            l_Std_Http_Headers_getAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2525_, 0, v___x_2524_);
        crate::leanh::lean_closure_set(v___f_2525_, 1, v_entries_2522_);
        v___x_2526_ = l_Std_Http_Headers_getAll___redArg___closed__9;
        v___x_2527_ = lean_array_get_size(v___x_2524_);
        v___x_2528_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2529_ = lean_mk_empty_array_with_capacity(v___x_2527_);
        v_entries_2530_ = l_Array_mapFinIdxM_map___redArg(
            v___x_2526_,
            v___x_2524_,
            v___f_2525_,
            v___x_2527_,
            v___x_2528_,
            v___x_2529_,
        );
        v___x_2531_ = lean_array_get_size(v_entries_2530_);
        v___x_2532_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2533_ = lean_nat_sub(v___x_2531_, v___x_2532_);
        v___x_2534_ = lean_nat_dec_lt(v___x_2533_, v___x_2531_);
        if v___x_2534_ == 0 {
            let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2533_);
            crate::leanh::lean_dec(v_entries_2530_);
            v___x_2535_ = crate::leanh::lean_box(0);
            return v___x_2535_;
        } else {
            let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2536_ = lean_array_fget(v_entries_2530_, v___x_2533_);
            crate::leanh::lean_dec(v___x_2533_);
            crate::leanh::lean_dec(v_entries_2530_);
            v___x_2537_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2537_, 0, v___x_2536_);
            return v___x_2537_;
        }
    }
}
pub unsafe fn l_Std_Http_Headers_getD(
    mut v_headers_2538_: *mut crate::leanh::LeanObject,
    mut v_name_2539_: *mut crate::leanh::LeanObject,
    mut v_d_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    v___f_2541_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2542_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    crate::leanh::lean_inc_ref(v_name_2539_);
    v___x_2543_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_2541_,
        v___f_2542_,
        v_name_2539_,
        v_headers_2538_,
    );
    if v___x_2543_ == 0 {
        crate::leanh::lean_dec_ref(v_name_2539_);
        crate::leanh::lean_inc_ref(v_d_2540_);
        return v_d_2540_;
    } else {
        let mut v_entries_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_entry_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_entries_2544_ = crate::leanh::lean_ctor_get(v_headers_2538_, 0);
        v_indexes_2545_ = crate::leanh::lean_ctor_get(v_headers_2538_, 1);
        v___x_2546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v___f_2541_,
            v___f_2542_,
            v_indexes_2545_,
            v_name_2539_,
        );
        v___x_2547_ = crate::leanh::lean_unsigned_to_nat(0);
        v_entry_2548_ = lean_array_fget(v___x_2546_, v___x_2547_);
        crate::leanh::lean_dec(v___x_2546_);
        v___x_2549_ = lean_array_fget_borrowed(v_entries_2544_, v_entry_2548_);
        crate::leanh::lean_dec(v_entry_2548_);
        v_snd_2550_ = crate::leanh::lean_ctor_get(v___x_2549_, 1);
        crate::leanh::lean_inc(v_snd_2550_);
        return v_snd_2550_;
    }
}
pub unsafe fn l_Std_Http_Headers_getD___boxed(
    mut v_headers_2551_: *mut crate::leanh::LeanObject,
    mut v_name_2552_: *mut crate::leanh::LeanObject,
    mut v_d_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2554_ = l_Std_Http_Headers_getD(v_headers_2551_, v_name_2552_, v_d_2553_);
    crate::leanh::lean_dec_ref(v_d_2553_);
    crate::leanh::lean_dec_ref(v_headers_2551_);
    return v_res_2554_;
}
pub unsafe fn _init_l_Std_Http_Headers_get_x21___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2559_ = l_Std_Http_Headers_get_x21___closed__3;
    v___x_2560_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2561_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_2562_ = l_Std_Http_Headers_get_x21___closed__2;
    v___x_2563_ = l_Std_Http_Headers_get_x21___closed__1;
    v___x_2564_ = l_mkPanicMessageWithDecl(
        v___x_2563_,
        v___x_2562_,
        v___x_2561_,
        v___x_2560_,
        v___x_2559_,
    );
    return v___x_2564_;
}
pub unsafe fn l_Std_Http_Headers_get_x21(
    mut v_headers_2565_: *mut crate::leanh::LeanObject,
    mut v_name_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    v___f_2567_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2568_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    crate::leanh::lean_inc_ref(v_name_2566_);
    v___x_2569_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_2567_,
        v___f_2568_,
        v_name_2566_,
        v_headers_2565_,
    );
    if v___x_2569_ == 0 {
        let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_name_2566_);
        v___x_2570_ = l_Std_Http_Headers_get_x21___closed__0;
        v___x_2571_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Http_Headers_get_x21___closed__4),
            core::ptr::addr_of_mut!(l_Std_Http_Headers_get_x21___closed__4_once),
            _init_l_Std_Http_Headers_get_x21___closed__4,
        );
        v___x_2572_ = l_panic___redArg(v___x_2570_, v___x_2571_);
        return v___x_2572_;
    } else {
        let mut v_entries_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_indexes_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_entry_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_entries_2573_ = crate::leanh::lean_ctor_get(v_headers_2565_, 0);
        v_indexes_2574_ = crate::leanh::lean_ctor_get(v_headers_2565_, 1);
        v___x_2575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
            v___f_2567_,
            v___f_2568_,
            v_indexes_2574_,
            v_name_2566_,
        );
        v___x_2576_ = crate::leanh::lean_unsigned_to_nat(0);
        v_entry_2577_ = lean_array_fget(v___x_2575_, v___x_2576_);
        crate::leanh::lean_dec(v___x_2575_);
        v___x_2578_ = lean_array_fget_borrowed(v_entries_2573_, v_entry_2577_);
        crate::leanh::lean_dec(v_entry_2577_);
        v_snd_2579_ = crate::leanh::lean_ctor_get(v___x_2578_, 1);
        crate::leanh::lean_inc(v_snd_2579_);
        return v_snd_2579_;
    }
}
pub unsafe fn l_Std_Http_Headers_get_x21___boxed(
    mut v_headers_2580_: *mut crate::leanh::LeanObject,
    mut v_name_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2582_ = l_Std_Http_Headers_get_x21(v_headers_2580_, v_name_2581_);
    crate::leanh::lean_dec_ref(v_headers_2580_);
    return v_res_2582_;
}
pub unsafe fn l_Std_Http_Headers_insert___lam__0(
    mut v_i_2583_: *mut crate::leanh::LeanObject,
    mut v_x_2584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2592_: u8 = 0;
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2584_) == 0 {
                    v___x_2585_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2586_ = lean_mk_empty_array_with_capacity(v___x_2585_);
                    v___x_2587_ = lean_array_push(v___x_2586_, v_i_2583_);
                    v___x_2588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2588_, 0, v___x_2587_);
                    return v___x_2588_;
                } else {
                    v_val_2589_ = crate::leanh::lean_ctor_get(v_x_2584_, 0);
                    v_isSharedCheck_2597_ = (!crate::leanh::lean_is_exclusive(v_x_2584_)) as u8;
                    if v_isSharedCheck_2597_ == 0 {
                        v___x_2591_ = v_x_2584_;
                        v_isShared_2592_ = v_isSharedCheck_2597_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2589_);
                        crate::leanh::lean_dec(v_x_2584_);
                        v___x_2591_ = crate::leanh::lean_box(0);
                        v_isShared_2592_ = v_isSharedCheck_2597_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2593_ = lean_array_push(v_val_2589_, v_i_2583_);
                if v_isShared_2592_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2591_, 0, v___x_2593_);
                    v___x_2595_ = v___x_2591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2596_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
                    v___x_2595_ = v_reuseFailAlloc_2596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_insert(
    mut v_headers_2598_: *mut crate::leanh::LeanObject,
    mut v_key_2599_: *mut crate::leanh::LeanObject,
    mut v_value_2600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___f_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entries_2601_ = crate::leanh::lean_ctor_get(v_headers_2598_, 0);
                v_indexes_2602_ = crate::leanh::lean_ctor_get(v_headers_2598_, 1);
                v_isSharedCheck_2616_ = (!crate::leanh::lean_is_exclusive(v_headers_2598_)) as u8;
                if v_isSharedCheck_2616_ == 0 {
                    v___x_2604_ = v_headers_2598_;
                    v_isShared_2605_ = v_isSharedCheck_2616_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_2602_);
                    crate::leanh::lean_inc(v_entries_2601_);
                    crate::leanh::lean_dec(v_headers_2598_);
                    v___x_2604_ = crate::leanh::lean_box(0);
                    v_isShared_2605_ = v_isSharedCheck_2616_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2606_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
                v___f_2607_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
                v_i_2608_ = lean_array_get_size(v_entries_2601_);
                v_f_2609_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Headers_insert___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v_f_2609_, 0, v_i_2608_);
                crate::leanh::lean_inc_ref(v_key_2599_);
                v___x_2610_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2610_, 0, v_key_2599_);
                crate::leanh::lean_ctor_set(v___x_2610_, 1, v_value_2600_);
                v_entries_2611_ = lean_array_push(v_entries_2601_, v___x_2610_);
                v_indexes_2612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_2606_,
                    v___f_2607_,
                    v_indexes_2602_,
                    v_key_2599_,
                    v_f_2609_,
                );
                if v_isShared_2605_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2604_, 1, v_indexes_2612_);
                    crate::leanh::lean_ctor_set(v___x_2604_, 0, v_entries_2611_);
                    v___x_2614_ = v___x_2604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2615_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_entries_2611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_indexes_2612_);
                    v___x_2614_ = v_reuseFailAlloc_2615_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_insert_x21(
    mut v_headers_2617_: *mut crate::leanh::LeanObject,
    mut v_name_2618_: *mut crate::leanh::LeanObject,
    mut v_value_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2624_: u8 = 0;
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entries_2620_ = crate::leanh::lean_ctor_get(v_headers_2617_, 0);
                v_indexes_2621_ = crate::leanh::lean_ctor_get(v_headers_2617_, 1);
                v_isSharedCheck_2637_ = (!crate::leanh::lean_is_exclusive(v_headers_2617_)) as u8;
                if v_isSharedCheck_2637_ == 0 {
                    v___x_2623_ = v_headers_2617_;
                    v_isShared_2624_ = v_isSharedCheck_2637_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_2621_);
                    crate::leanh::lean_inc(v_entries_2620_);
                    crate::leanh::lean_dec(v_headers_2617_);
                    v___x_2623_ = crate::leanh::lean_box(0);
                    v_isShared_2624_ = v_isSharedCheck_2637_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2625_ = l_Std_Http_Header_Name_ofString_x21(v_name_2618_);
                v___x_2626_ = l_Std_Http_Header_Value_ofString_x21(v_value_2619_);
                v___f_2627_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
                v___f_2628_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
                v_i_2629_ = lean_array_get_size(v_entries_2620_);
                v_f_2630_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Headers_insert___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v_f_2630_, 0, v_i_2629_);
                crate::leanh::lean_inc_ref(v___x_2625_);
                v___x_2631_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2631_, 0, v___x_2625_);
                crate::leanh::lean_ctor_set(v___x_2631_, 1, v___x_2626_);
                v_entries_2632_ = lean_array_push(v_entries_2620_, v___x_2631_);
                v_indexes_2633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_2627_,
                    v___f_2628_,
                    v_indexes_2621_,
                    v___x_2625_,
                    v_f_2630_,
                );
                if v_isShared_2624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2623_, 1, v_indexes_2633_);
                    crate::leanh::lean_ctor_set(v___x_2623_, 0, v_entries_2632_);
                    v___x_2635_ = v___x_2623_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2636_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_entries_2632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_indexes_2633_);
                    v___x_2635_ = v_reuseFailAlloc_2636_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_insert_x3f(
    mut v_headers_2638_: *mut crate::leanh::LeanObject,
    mut v_name_2639_: *mut crate::leanh::LeanObject,
    mut v_value_2640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2649_: u8 = 0;
    let mut v_entries_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___f_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2668_: u8 = 0;
    let mut v_isSharedCheck_2669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2641_ = l_Std_Http_Header_Name_ofString_x3f(v_name_2639_);
                if crate::leanh::lean_obj_tag(v___x_2641_) == 0 {
                    crate::leanh::lean_dec_ref(v_value_2640_);
                    crate::leanh::lean_dec_ref(v_headers_2638_);
                    v___x_2642_ = crate::leanh::lean_box(0);
                    return v___x_2642_;
                } else {
                    v_val_2643_ = crate::leanh::lean_ctor_get(v___x_2641_, 0);
                    crate::leanh::lean_inc(v_val_2643_);
                    crate::leanh::lean_dec_ref_known(v___x_2641_, 1);
                    v___x_2644_ = l_Std_Http_Header_Value_ofString_x3f(v_value_2640_);
                    if crate::leanh::lean_obj_tag(v___x_2644_) == 0 {
                        crate::leanh::lean_dec(v_val_2643_);
                        crate::leanh::lean_dec_ref(v_headers_2638_);
                        v___x_2645_ = crate::leanh::lean_box(0);
                        return v___x_2645_;
                    } else {
                        v_val_2646_ = crate::leanh::lean_ctor_get(v___x_2644_, 0);
                        v_isSharedCheck_2669_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2644_)) as u8;
                        if v_isSharedCheck_2669_ == 0 {
                            v___x_2648_ = v___x_2644_;
                            v_isShared_2649_ = v_isSharedCheck_2669_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2646_);
                            crate::leanh::lean_dec(v___x_2644_);
                            v___x_2648_ = crate::leanh::lean_box(0);
                            v_isShared_2649_ = v_isSharedCheck_2669_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_entries_2650_ = crate::leanh::lean_ctor_get(v_headers_2638_, 0);
                v_indexes_2651_ = crate::leanh::lean_ctor_get(v_headers_2638_, 1);
                v_isSharedCheck_2668_ = (!crate::leanh::lean_is_exclusive(v_headers_2638_)) as u8;
                if v_isSharedCheck_2668_ == 0 {
                    v___x_2653_ = v_headers_2638_;
                    v_isShared_2654_ = v_isSharedCheck_2668_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_2651_);
                    crate::leanh::lean_inc(v_entries_2650_);
                    crate::leanh::lean_dec(v_headers_2638_);
                    v___x_2653_ = crate::leanh::lean_box(0);
                    v_isShared_2654_ = v_isSharedCheck_2668_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2655_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
                v___f_2656_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
                v_i_2657_ = lean_array_get_size(v_entries_2650_);
                v_f_2658_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Headers_insert___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v_f_2658_, 0, v_i_2657_);
                crate::leanh::lean_inc(v_val_2643_);
                v___x_2659_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2659_, 0, v_val_2643_);
                crate::leanh::lean_ctor_set(v___x_2659_, 1, v_val_2646_);
                v_entries_2660_ = lean_array_push(v_entries_2650_, v___x_2659_);
                v_indexes_2661_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_2655_,
                    v___f_2656_,
                    v_indexes_2651_,
                    v_val_2643_,
                    v_f_2658_,
                );
                if v_isShared_2654_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2653_, 1, v_indexes_2661_);
                    crate::leanh::lean_ctor_set(v___x_2653_, 0, v_entries_2660_);
                    v___x_2663_ = v___x_2653_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_entries_2660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_indexes_2661_);
                    v___x_2663_ = v_reuseFailAlloc_2667_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2648_, 0, v___x_2663_);
                    v___x_2665_ = v___x_2648_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2666_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
                    v___x_2665_ = v_reuseFailAlloc_2666_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_insertMany___lam__1(
    mut v_key_2670_: *mut crate::leanh::LeanObject,
    mut v___f_2671_: *mut crate::leanh::LeanObject,
    mut v___f_2672_: *mut crate::leanh::LeanObject,
    mut v_x1_2673_: *mut crate::leanh::LeanObject,
    mut v_x2_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v_i_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entries_2675_ = crate::leanh::lean_ctor_get(v_x1_2673_, 0);
                v_indexes_2676_ = crate::leanh::lean_ctor_get(v_x1_2673_, 1);
                v_isSharedCheck_2688_ = (!crate::leanh::lean_is_exclusive(v_x1_2673_)) as u8;
                if v_isSharedCheck_2688_ == 0 {
                    v___x_2678_ = v_x1_2673_;
                    v_isShared_2679_ = v_isSharedCheck_2688_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_2676_);
                    crate::leanh::lean_inc(v_entries_2675_);
                    crate::leanh::lean_dec(v_x1_2673_);
                    v___x_2678_ = crate::leanh::lean_box(0);
                    v_isShared_2679_ = v_isSharedCheck_2688_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_2680_ = lean_array_get_size(v_entries_2675_);
                v_f_2681_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Headers_insert___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v_f_2681_, 0, v_i_2680_);
                crate::leanh::lean_inc_ref(v_key_2670_);
                v___x_2682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2682_, 0, v_key_2670_);
                crate::leanh::lean_ctor_set(v___x_2682_, 1, v_x2_2674_);
                v_entries_2683_ = lean_array_push(v_entries_2675_, v___x_2682_);
                v_indexes_2684_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_2671_,
                    v___f_2672_,
                    v_indexes_2676_,
                    v_key_2670_,
                    v_f_2681_,
                );
                if v_isShared_2679_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2678_, 1, v_indexes_2684_);
                    crate::leanh::lean_ctor_set(v___x_2678_, 0, v_entries_2683_);
                    v___x_2686_ = v___x_2678_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_entries_2683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_indexes_2684_);
                    v___x_2686_ = v_reuseFailAlloc_2687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_insertMany(
    mut v_headers_2689_: *mut crate::leanh::LeanObject,
    mut v_key_2690_: *mut crate::leanh::LeanObject,
    mut v_values_2691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: u8 = 0;
    v___x_2692_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2693_ = lean_array_get_size(v_values_2691_);
    v___x_2694_ = l_Std_Http_Headers_getAll___redArg___closed__9;
    v___x_2695_ = lean_nat_dec_lt(v___x_2692_, v___x_2693_);
    if v___x_2695_ == 0 {
        crate::leanh::lean_dec_ref(v_values_2691_);
        crate::leanh::lean_dec_ref(v_key_2690_);
        return v_headers_2689_;
    } else {
        let mut v___f_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2699_: u8 = 0;
        v___f_2696_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
        v___f_2697_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
        v___f_2698_ = crate::leanh::lean_alloc_closure(
            l_Std_Http_Headers_insertMany___lam__1 as *mut core::ffi::c_void,
            5,
            3,
        );
        crate::leanh::lean_closure_set(v___f_2698_, 0, v_key_2690_);
        crate::leanh::lean_closure_set(v___f_2698_, 1, v___f_2696_);
        crate::leanh::lean_closure_set(v___f_2698_, 2, v___f_2697_);
        v___x_2699_ = lean_nat_dec_le(v___x_2693_, v___x_2693_);
        if v___x_2699_ == 0 {
            if v___x_2695_ == 0 {
                crate::leanh::lean_dec_ref(v___f_2698_);
                crate::leanh::lean_dec_ref(v_values_2691_);
                return v_headers_2689_;
            } else {
                let mut v___x_2700_: usize = 0;
                let mut v___x_2701_: usize = 0;
                let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2700_ = 0usize;
                v___x_2701_ = lean_usize_of_nat(v___x_2693_);
                v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2694_,
                    v___f_2698_,
                    v_values_2691_,
                    v___x_2700_,
                    v___x_2701_,
                    v_headers_2689_,
                );
                return v___x_2702_;
            }
        } else {
            let mut v___x_2703_: usize = 0;
            let mut v___x_2704_: usize = 0;
            let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2703_ = 0usize;
            v___x_2704_ = lean_usize_of_nat(v___x_2693_);
            v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2694_,
                v___f_2698_,
                v_values_2691_,
                v___x_2703_,
                v___x_2704_,
                v_headers_2689_,
            );
            return v___x_2705_;
        }
    }
}
pub unsafe fn _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2708_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedHeaders_default___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_instInhabitedHeaders_default___closed__2_once),
        _init_l_Std_Http_instInhabitedHeaders_default___closed__2,
    );
    v___x_2709_ =
        l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0;
    v___x_2710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2710_, 0, v___x_2709_);
    crate::leanh::lean_ctor_set(v___x_2710_, 1, v___x_2708_);
    return v___x_2710_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(
    mut v_00_u03b2_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1), core::ptr::addr_of_mut!(l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1_once), _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1);
    return v___x_2712_;
}
pub unsafe fn _init_l_Std_Http_Headers_empty___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2713_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(
        crate::leanh::lean_box(0),
    );
    return v___x_2713_;
}
pub unsafe fn _init_l_Std_Http_Headers_empty() -> *mut crate::leanh::LeanObject {
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2714_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0_once),
        _init_l_Std_Http_Headers_empty___closed__0,
    );
    return v___x_2714_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(
    mut v_i_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: *mut crate::leanh::LeanObject,
    mut v_x_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2728_: u8 = 0;
    let mut v_tail_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2717_) == 0 {
                    v___x_2718_ = crate::leanh::lean_box(0);
                    v___x_2719_ = l_Std_Http_Headers_insert___lam__0(v_i_2715_, v___x_2718_);
                    v_val_2720_ = crate::leanh::lean_ctor_get(v___x_2719_, 0);
                    crate::leanh::lean_inc(v_val_2720_);
                    crate::leanh::lean_dec(v___x_2719_);
                    v___x_2721_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2721_, 0, v_a_2716_);
                    crate::leanh::lean_ctor_set(v___x_2721_, 1, v_val_2720_);
                    crate::leanh::lean_ctor_set(v___x_2721_, 2, v_x_2717_);
                    return v___x_2721_;
                } else {
                    v_key_2722_ = crate::leanh::lean_ctor_get(v_x_2717_, 0);
                    v_value_2723_ = crate::leanh::lean_ctor_get(v_x_2717_, 1);
                    v_tail_2724_ = crate::leanh::lean_ctor_get(v_x_2717_, 2);
                    v_isSharedCheck_2739_ = (!crate::leanh::lean_is_exclusive(v_x_2717_)) as u8;
                    if v_isSharedCheck_2739_ == 0 {
                        v___x_2726_ = v_x_2717_;
                        v_isShared_2727_ = v_isSharedCheck_2739_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2724_);
                        crate::leanh::lean_inc(v_value_2723_);
                        crate::leanh::lean_inc(v_key_2722_);
                        crate::leanh::lean_dec(v_x_2717_);
                        v___x_2726_ = crate::leanh::lean_box(0);
                        v_isShared_2727_ = v_isSharedCheck_2739_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2728_ = lean_string_dec_eq(v_key_2722_, v_a_2716_);
                if v___x_2728_ == 0 {
                    v_tail_2729_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(v_i_2715_, v_a_2716_, v_tail_2724_);
                    if v_isShared_2727_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2726_, 2, v_tail_2729_);
                        v___x_2731_ = v___x_2726_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2732_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_key_2722_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_value_2723_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_tail_2729_);
                        v___x_2731_ = v_reuseFailAlloc_2732_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_key_2722_);
                    v___x_2733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2733_, 0, v_value_2723_);
                    v___x_2734_ = l_Std_Http_Headers_insert___lam__0(v_i_2715_, v___x_2733_);
                    v_val_2735_ = crate::leanh::lean_ctor_get(v___x_2734_, 0);
                    crate::leanh::lean_inc(v_val_2735_);
                    crate::leanh::lean_dec(v___x_2734_);
                    if v_isShared_2727_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2726_, 1, v_val_2735_);
                        crate::leanh::lean_ctor_set(v___x_2726_, 0, v_a_2716_);
                        v___x_2737_ = v___x_2726_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2738_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2716_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_val_2735_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_tail_2724_);
                        v___x_2737_ = v_reuseFailAlloc_2738_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2731_;
            }
            3 => {
                return v___x_2737_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_x_2740_: *mut crate::leanh::LeanObject,
    mut v_x_2741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: u64 = 0;
    let mut v___x_2750_: u64 = 0;
    let mut v___x_2751_: u64 = 0;
    let mut v_fold_2752_: u64 = 0;
    let mut v___x_2753_: u64 = 0;
    let mut v___x_2754_: u64 = 0;
    let mut v___x_2755_: u64 = 0;
    let mut v___x_2756_: usize = 0;
    let mut v___x_2757_: usize = 0;
    let mut v___x_2758_: usize = 0;
    let mut v___x_2759_: usize = 0;
    let mut v___x_2760_: usize = 0;
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2741_) == 0 {
                    return v_x_2740_;
                } else {
                    v_key_2742_ = crate::leanh::lean_ctor_get(v_x_2741_, 0);
                    v_value_2743_ = crate::leanh::lean_ctor_get(v_x_2741_, 1);
                    v_tail_2744_ = crate::leanh::lean_ctor_get(v_x_2741_, 2);
                    v_isSharedCheck_2767_ = (!crate::leanh::lean_is_exclusive(v_x_2741_)) as u8;
                    if v_isSharedCheck_2767_ == 0 {
                        v___x_2746_ = v_x_2741_;
                        v_isShared_2747_ = v_isSharedCheck_2767_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2744_);
                        crate::leanh::lean_inc(v_value_2743_);
                        crate::leanh::lean_inc(v_key_2742_);
                        crate::leanh::lean_dec(v_x_2741_);
                        v___x_2746_ = crate::leanh::lean_box(0);
                        v_isShared_2747_ = v_isSharedCheck_2767_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2748_ = lean_array_get_size(v_x_2740_);
                v___x_2749_ = lean_string_hash(v_key_2742_);
                v___x_2750_ = 32u64;
                v___x_2751_ = lean_uint64_shift_right(v___x_2749_, v___x_2750_);
                v_fold_2752_ = lean_uint64_xor(v___x_2749_, v___x_2751_);
                v___x_2753_ = 16u64;
                v___x_2754_ = lean_uint64_shift_right(v_fold_2752_, v___x_2753_);
                v___x_2755_ = lean_uint64_xor(v_fold_2752_, v___x_2754_);
                v___x_2756_ = lean_uint64_to_usize(v___x_2755_);
                v___x_2757_ = lean_usize_of_nat(v___x_2748_);
                v___x_2758_ = 1usize;
                v___x_2759_ = lean_usize_sub(v___x_2757_, v___x_2758_);
                v___x_2760_ = lean_usize_land(v___x_2756_, v___x_2759_);
                v___x_2761_ = lean_array_uget_borrowed(v_x_2740_, v___x_2760_);
                crate::leanh::lean_inc(v___x_2761_);
                if v_isShared_2747_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2746_, 2, v___x_2761_);
                    v___x_2763_ = v___x_2746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2766_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_key_2742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_value_2743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 2, v___x_2761_);
                    v___x_2763_ = v_reuseFailAlloc_2766_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2764_ = lean_array_uset(v_x_2740_, v___x_2760_, v___x_2763_);
                v_x_2740_ = v___x_2764_;
                v_x_2741_ = v_tail_2744_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_i_2768_: *mut crate::leanh::LeanObject,
    mut v_source_2769_: *mut crate::leanh::LeanObject,
    mut v_target_2770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v_es_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2771_ = lean_array_get_size(v_source_2769_);
                v___x_2772_ = lean_nat_dec_lt(v_i_2768_, v___x_2771_);
                if v___x_2772_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2769_);
                    crate::leanh::lean_dec(v_i_2768_);
                    return v_target_2770_;
                } else {
                    v_es_2773_ = lean_array_fget(v_source_2769_, v_i_2768_);
                    v___x_2774_ = crate::leanh::lean_box(0);
                    v_source_2775_ = lean_array_fset(v_source_2769_, v_i_2768_, v___x_2774_);
                    v_target_2776_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_2770_, v_es_2773_);
                    v___x_2777_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2778_ = lean_nat_add(v_i_2768_, v___x_2777_);
                    crate::leanh::lean_dec(v_i_2768_);
                    v_i_2768_ = v___x_2778_;
                    v_source_2769_ = v_source_2775_;
                    v_target_2770_ = v_target_2776_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(
    mut v_data_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2781_ = lean_array_get_size(v_data_2780_);
    v___x_2782_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2783_ = lean_nat_mul(v___x_2781_, v___x_2782_);
    v___x_2784_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2785_ = crate::leanh::lean_box(0);
    v___x_2786_ = lean_mk_array(v_nbuckets_2783_, v___x_2785_);
    v___x_2787_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(v___x_2784_, v_data_2780_, v___x_2786_);
    return v___x_2787_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(
    mut v_a_2788_: *mut crate::leanh::LeanObject,
    mut v_x_2789_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2790_: u8 = 0;
    let mut v_key_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2789_) == 0 {
                    v___x_2790_ = 0;
                    return v___x_2790_;
                } else {
                    v_key_2791_ = crate::leanh::lean_ctor_get(v_x_2789_, 0);
                    v_tail_2792_ = crate::leanh::lean_ctor_get(v_x_2789_, 2);
                    v___x_2793_ = lean_string_dec_eq(v_key_2791_, v_a_2788_);
                    if v___x_2793_ == 0 {
                        v_x_2789_ = v_tail_2792_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2793_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_a_2795_: *mut crate::leanh::LeanObject,
    mut v_x_2796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2797_: u8 = 0;
    let mut v_r_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_2795_, v_x_2796_);
    crate::leanh::lean_dec(v_x_2796_);
    crate::leanh::lean_dec_ref(v_a_2795_);
    v_r_2798_ = crate::leanh::lean_box((v_res_2797_) as usize);
    return v_r_2798_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(
    mut v_i_2799_: *mut crate::leanh::LeanObject,
    mut v_m_2800_: *mut crate::leanh::LeanObject,
    mut v_a_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2806_: u8 = 0;
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u64 = 0;
    let mut v___x_2809_: u64 = 0;
    let mut v___x_2810_: u64 = 0;
    let mut v_fold_2811_: u64 = 0;
    let mut v___x_2812_: u64 = 0;
    let mut v___x_2813_: u64 = 0;
    let mut v___x_2814_: u64 = 0;
    let mut v___x_2815_: usize = 0;
    let mut v___x_2816_: usize = 0;
    let mut v___x_2817_: usize = 0;
    let mut v___x_2818_: usize = 0;
    let mut v___x_2819_: usize = 0;
    let mut v_bkt_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: u8 = 0;
    let mut v_val_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: u8 = 0;
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2853_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2802_ = crate::leanh::lean_ctor_get(v_m_2800_, 0);
                v_buckets_2803_ = crate::leanh::lean_ctor_get(v_m_2800_, 1);
                v_isSharedCheck_2853_ = (!crate::leanh::lean_is_exclusive(v_m_2800_)) as u8;
                if v_isSharedCheck_2853_ == 0 {
                    v___x_2805_ = v_m_2800_;
                    v_isShared_2806_ = v_isSharedCheck_2853_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2803_);
                    crate::leanh::lean_inc(v_size_2802_);
                    crate::leanh::lean_dec(v_m_2800_);
                    v___x_2805_ = crate::leanh::lean_box(0);
                    v_isShared_2806_ = v_isSharedCheck_2853_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2807_ = lean_array_get_size(v_buckets_2803_);
                v___x_2808_ = lean_string_hash(v_a_2801_);
                v___x_2809_ = 32u64;
                v___x_2810_ = lean_uint64_shift_right(v___x_2808_, v___x_2809_);
                v_fold_2811_ = lean_uint64_xor(v___x_2808_, v___x_2810_);
                v___x_2812_ = 16u64;
                v___x_2813_ = lean_uint64_shift_right(v_fold_2811_, v___x_2812_);
                v___x_2814_ = lean_uint64_xor(v_fold_2811_, v___x_2813_);
                v___x_2815_ = lean_uint64_to_usize(v___x_2814_);
                v___x_2816_ = lean_usize_of_nat(v___x_2807_);
                v___x_2817_ = 1usize;
                v___x_2818_ = lean_usize_sub(v___x_2816_, v___x_2817_);
                v___x_2819_ = lean_usize_land(v___x_2815_, v___x_2818_);
                v_bkt_2820_ = lean_array_uget_borrowed(v_buckets_2803_, v___x_2819_);
                v___x_2821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_2801_, v_bkt_2820_);
                if v___x_2821_ == 0 {
                    v___x_2822_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2823_ = lean_mk_empty_array_with_capacity(v___x_2822_);
                    v___x_2824_ = lean_array_push(v___x_2823_, v_i_2799_);
                    v_size_x27_2825_ = lean_nat_add(v_size_2802_, v___x_2822_);
                    crate::leanh::lean_dec(v_size_2802_);
                    crate::leanh::lean_inc(v_bkt_2820_);
                    v___x_2826_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v_a_2801_);
                    crate::leanh::lean_ctor_set(v___x_2826_, 1, v___x_2824_);
                    crate::leanh::lean_ctor_set(v___x_2826_, 2, v_bkt_2820_);
                    v_buckets_x27_2827_ =
                        lean_array_uset(v_buckets_2803_, v___x_2819_, v___x_2826_);
                    v___x_2828_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2829_ = lean_nat_mul(v_size_x27_2825_, v___x_2828_);
                    v___x_2830_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2831_ = lean_nat_div(v___x_2829_, v___x_2830_);
                    crate::leanh::lean_dec(v___x_2829_);
                    v___x_2832_ = lean_array_get_size(v_buckets_x27_2827_);
                    v___x_2833_ = lean_nat_dec_le(v___x_2831_, v___x_2832_);
                    crate::leanh::lean_dec(v___x_2831_);
                    if v___x_2833_ == 0 {
                        v_val_2834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(v_buckets_x27_2827_);
                        if v_isShared_2806_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2805_, 1, v_val_2834_);
                            crate::leanh::lean_ctor_set(v___x_2805_, 0, v_size_x27_2825_);
                            v___x_2836_ = v___x_2805_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2837_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2837_,
                                0,
                                v_size_x27_2825_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_val_2834_);
                            v___x_2836_ = v_reuseFailAlloc_2837_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2806_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2805_, 1, v_buckets_x27_2827_);
                            crate::leanh::lean_ctor_set(v___x_2805_, 0, v_size_x27_2825_);
                            v___x_2839_ = v___x_2805_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2840_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2840_,
                                0,
                                v_size_x27_2825_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2840_,
                                1,
                                v_buckets_x27_2827_,
                            );
                            v___x_2839_ = v_reuseFailAlloc_2840_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2820_);
                    v___x_2841_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2842_ =
                        lean_array_uset(v_buckets_2803_, v___x_2819_, v___x_2841_);
                    crate::leanh::lean_inc_ref(v_a_2801_);
                    v_bkt_x27_2843_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(v_i_2799_, v_a_2801_, v_bkt_2820_);
                    v___x_2850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_2801_, v_bkt_x27_2843_);
                    crate::leanh::lean_dec_ref(v_a_2801_);
                    if v___x_2850_ == 0 {
                        v___x_2851_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2852_ = lean_nat_sub(v_size_2802_, v___x_2851_);
                        crate::leanh::lean_dec(v_size_2802_);
                        v___y_2845_ = v___x_2852_;
                        state = 4;
                        continue;
                    } else {
                        v___y_2845_ = v_size_2802_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2836_;
            }
            3 => {
                return v___x_2839_;
            }
            4 => {
                v___x_2846_ = lean_array_uset(v_buckets_x27_2842_, v___x_2819_, v_bkt_x27_2843_);
                if v_isShared_2806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2805_, 1, v___x_2846_);
                    crate::leanh::lean_ctor_set(v___x_2805_, 0, v___y_2845_);
                    v___x_2848_ = v___x_2805_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2849_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___y_2845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 1, v___x_2846_);
                    v___x_2848_ = v_reuseFailAlloc_2849_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(
    mut v_x_2854_: *mut crate::leanh::LeanObject,
    mut v_x_2855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v_i_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2855_) == 0 {
                    return v_x_2854_;
                } else {
                    v_head_2856_ = crate::leanh::lean_ctor_get(v_x_2855_, 0);
                    crate::leanh::lean_inc(v_head_2856_);
                    v_tail_2857_ = crate::leanh::lean_ctor_get(v_x_2855_, 1);
                    crate::leanh::lean_inc(v_tail_2857_);
                    crate::leanh::lean_dec_ref_known(v_x_2855_, 2);
                    v_fst_2858_ = crate::leanh::lean_ctor_get(v_head_2856_, 0);
                    crate::leanh::lean_inc(v_fst_2858_);
                    v_entries_2859_ = crate::leanh::lean_ctor_get(v_x_2854_, 0);
                    v_indexes_2860_ = crate::leanh::lean_ctor_get(v_x_2854_, 1);
                    v_isSharedCheck_2871_ = (!crate::leanh::lean_is_exclusive(v_x_2854_)) as u8;
                    if v_isSharedCheck_2871_ == 0 {
                        v___x_2862_ = v_x_2854_;
                        v_isShared_2863_ = v_isSharedCheck_2871_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_indexes_2860_);
                        crate::leanh::lean_inc(v_entries_2859_);
                        crate::leanh::lean_dec(v_x_2854_);
                        v___x_2862_ = crate::leanh::lean_box(0);
                        v_isShared_2863_ = v_isSharedCheck_2871_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_i_2864_ = lean_array_get_size(v_entries_2859_);
                v_entries_2865_ = lean_array_push(v_entries_2859_, v_head_2856_);
                v_indexes_2866_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_2864_, v_indexes_2860_, v_fst_2858_);
                if v_isShared_2863_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2862_, 1, v_indexes_2866_);
                    crate::leanh::lean_ctor_set(v___x_2862_, 0, v_entries_2865_);
                    v___x_2868_ = v___x_2862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2870_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_entries_2865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_indexes_2866_);
                    v___x_2868_ = v_reuseFailAlloc_2870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_2854_ = v___x_2868_;
                v_x_2855_ = v_tail_2857_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(
        crate::leanh::lean_box(0),
    );
    return v___x_2872_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(
    mut v_pairs_2873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2874_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0_once), _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0);
    v___x_2875_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v___x_2874_, v_pairs_2873_);
    return v___x_2875_;
}
pub unsafe fn l_Std_Http_Headers_ofList(
    mut v_pairs_2876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2877_ =
        l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(
            v_pairs_2876_,
        );
    return v___x_2877_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0(
    mut v_00_u03b2_2878_: *mut crate::leanh::LeanObject,
    mut v_inst_2879_: *mut crate::leanh::LeanObject,
    mut v_inst_2880_: *mut crate::leanh::LeanObject,
    mut v_pairs_2881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ =
        l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(
            v_pairs_2881_,
        );
    return v___x_2882_;
}
pub unsafe fn l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(
    mut v_00_u03b2_2883_: *mut crate::leanh::LeanObject,
    mut v_x_2884_: *mut crate::leanh::LeanObject,
    mut v_x_2885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2886_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_x_2884_, v_x_2885_);
    return v___x_2886_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2887_: *mut crate::leanh::LeanObject,
    mut v_a_2888_: *mut crate::leanh::LeanObject,
    mut v_x_2889_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2890_: u8 = 0;
    v___x_2890_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_2888_, v_x_2889_);
    return v___x_2890_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2891_: *mut crate::leanh::LeanObject,
    mut v_a_2892_: *mut crate::leanh::LeanObject,
    mut v_x_2893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2894_: u8 = 0;
    let mut v_r_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2894_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(v_00_u03b2_2891_, v_a_2892_, v_x_2893_);
    crate::leanh::lean_dec(v_x_2893_);
    crate::leanh::lean_dec_ref(v_a_2892_);
    v_r_2895_ = crate::leanh::lean_box((v_res_2894_) as usize);
    return v_r_2895_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2896_: *mut crate::leanh::LeanObject,
    mut v_data_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2898_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(v_data_2897_);
    return v___x_2898_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_2899_: *mut crate::leanh::LeanObject,
    mut v_i_2900_: *mut crate::leanh::LeanObject,
    mut v_source_2901_: *mut crate::leanh::LeanObject,
    mut v_target_2902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2903_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(v_i_2900_, v_source_2901_, v_target_2902_);
    return v___x_2903_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b2_2904_: *mut crate::leanh::LeanObject,
    mut v_x_2905_: *mut crate::leanh::LeanObject,
    mut v_x_2906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2907_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_2905_, v_x_2906_);
    return v___x_2907_;
}
pub unsafe fn l_Std_Http_Headers_contains(
    mut v_headers_2908_: *mut crate::leanh::LeanObject,
    mut v_name_2909_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_indexes_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: u8 = 0;
    v_indexes_2910_ = crate::leanh::lean_ctor_get(v_headers_2908_, 1);
    v___f_2911_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_2912_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    v___x_2913_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___f_2911_,
        v___f_2912_,
        v_indexes_2910_,
        v_name_2909_,
    );
    return v___x_2913_;
}
pub unsafe fn l_Std_Http_Headers_contains___boxed(
    mut v_headers_2914_: *mut crate::leanh::LeanObject,
    mut v_name_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2916_: u8 = 0;
    let mut v_r_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2916_ = l_Std_Http_Headers_contains(v_headers_2914_, v_name_2915_);
    crate::leanh::lean_dec_ref(v_headers_2914_);
    v_r_2917_ = crate::leanh::lean_box((v_res_2916_) as usize);
    return v_r_2917_;
}
pub unsafe fn l_Std_Http_Headers_erase___lam__1(
    mut v___f_2918_: *mut crate::leanh::LeanObject,
    mut v___f_2919_: *mut crate::leanh::LeanObject,
    mut v_x1_2920_: *mut crate::leanh::LeanObject,
    mut v_x2_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v_i_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2922_ = crate::leanh::lean_ctor_get(v_x2_2921_, 0);
                crate::leanh::lean_inc(v_fst_2922_);
                v_entries_2923_ = crate::leanh::lean_ctor_get(v_x1_2920_, 0);
                v_indexes_2924_ = crate::leanh::lean_ctor_get(v_x1_2920_, 1);
                v_isSharedCheck_2935_ = (!crate::leanh::lean_is_exclusive(v_x1_2920_)) as u8;
                if v_isSharedCheck_2935_ == 0 {
                    v___x_2926_ = v_x1_2920_;
                    v_isShared_2927_ = v_isSharedCheck_2935_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_2924_);
                    crate::leanh::lean_inc(v_entries_2923_);
                    crate::leanh::lean_dec(v_x1_2920_);
                    v___x_2926_ = crate::leanh::lean_box(0);
                    v_isShared_2927_ = v_isSharedCheck_2935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_i_2928_ = lean_array_get_size(v_entries_2923_);
                v_f_2929_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Headers_insert___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v_f_2929_, 0, v_i_2928_);
                v_entries_2930_ = lean_array_push(v_entries_2923_, v_x2_2921_);
                v_indexes_2931_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_2918_,
                    v___f_2919_,
                    v_indexes_2924_,
                    v_fst_2922_,
                    v_f_2929_,
                );
                if v_isShared_2927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2926_, 1, v_indexes_2931_);
                    crate::leanh::lean_ctor_set(v___x_2926_, 0, v_entries_2930_);
                    v___x_2933_ = v___x_2926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_entries_2930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_indexes_2931_);
                    v___x_2933_ = v_reuseFailAlloc_2934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_erase___lam__0(
    mut v_name_2936_: *mut crate::leanh::LeanObject,
    mut v_x1_2937_: *mut crate::leanh::LeanObject,
    mut v_x2_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    v_fst_2939_ = crate::leanh::lean_ctor_get(v_x2_2938_, 0);
    v___x_2940_ = lean_string_dec_eq(v_fst_2939_, v_name_2936_);
    if v___x_2940_ == 0 {
        let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2941_ = lean_array_push(v_x1_2937_, v_x2_2938_);
        return v___x_2941_;
    } else {
        crate::leanh::lean_dec_ref(v_x2_2938_);
        return v_x1_2937_;
    }
}
pub unsafe fn l_Std_Http_Headers_erase___lam__0___boxed(
    mut v_name_2942_: *mut crate::leanh::LeanObject,
    mut v_x1_2943_: *mut crate::leanh::LeanObject,
    mut v_x2_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2945_ = l_Std_Http_Headers_erase___lam__0(v_name_2942_, v_x1_2943_, v_x2_2944_);
    crate::leanh::lean_dec_ref(v_name_2942_);
    return v_res_2945_;
}
pub unsafe fn _init_l_Std_Http_Headers_erase___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___f_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2949_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    v___f_2950_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___x_2951_ = l_Std_Internal_IndexMultiMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2950_,
        v___f_2949_,
    );
    return v___x_2951_;
}
pub unsafe fn l_Std_Http_Headers_erase(
    mut v_headers_2952_: *mut crate::leanh::LeanObject,
    mut v_name_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v_entries_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: usize = 0;
    let mut v___x_2968_: usize = 0;
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: usize = 0;
    let mut v___x_2971_: usize = 0;
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: u8 = 0;
    let mut v___f_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: u8 = 0;
    let mut v___x_2979_: usize = 0;
    let mut v___x_2980_: usize = 0;
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: usize = 0;
    let mut v___x_2983_: usize = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2954_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
                v___f_2955_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
                crate::leanh::lean_inc_ref(v_name_2953_);
                v___x_2956_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v___f_2954_,
                    v___f_2955_,
                    v_name_2953_,
                    v_headers_2952_,
                );
                if v___x_2956_ == 0 {
                    crate::leanh::lean_dec_ref(v_name_2953_);
                    return v_headers_2952_;
                } else {
                    v_entries_2957_ = crate::leanh::lean_ctor_get(v_headers_2952_, 0);
                    crate::leanh::lean_inc_ref(v_entries_2957_);
                    crate::leanh::lean_dec_ref(v_headers_2952_);
                    v___f_2958_ = l_Std_Http_Headers_erase___closed__0;
                    v___x_2959_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Headers_erase___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Http_Headers_erase___closed__1_once),
                        _init_l_Std_Http_Headers_erase___closed__1,
                    );
                    v___x_2960_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2973_ = lean_array_get_size(v_entries_2957_);
                    v___x_2974_ = l_Std_Http_instInhabitedHeaders_default___closed__0;
                    v___x_2975_ = l_Std_Http_Headers_getAll___redArg___closed__9;
                    v___x_2976_ = lean_nat_dec_lt(v___x_2960_, v___x_2973_);
                    if v___x_2976_ == 0 {
                        crate::leanh::lean_dec_ref(v_entries_2957_);
                        crate::leanh::lean_dec_ref(v_name_2953_);
                        v___y_2962_ = v___x_2974_;
                        state = 1;
                        continue;
                    } else {
                        v___f_2977_ = crate::leanh::lean_alloc_closure(
                            l_Std_Http_Headers_erase___lam__0___boxed as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_2977_, 0, v_name_2953_);
                        v___x_2978_ = lean_nat_dec_le(v___x_2973_, v___x_2973_);
                        if v___x_2978_ == 0 {
                            if v___x_2976_ == 0 {
                                crate::leanh::lean_dec_ref(v___f_2977_);
                                crate::leanh::lean_dec_ref(v_entries_2957_);
                                v___y_2962_ = v___x_2974_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2979_ = 0usize;
                                v___x_2980_ = lean_usize_of_nat(v___x_2973_);
                                v___x_2981_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_2975_,
                                        v___f_2977_,
                                        v_entries_2957_,
                                        v___x_2979_,
                                        v___x_2980_,
                                        v___x_2974_,
                                    );
                                v___y_2962_ = v___x_2981_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2982_ = 0usize;
                            v___x_2983_ = lean_usize_of_nat(v___x_2973_);
                            v___x_2984_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_2975_,
                                    v___f_2977_,
                                    v_entries_2957_,
                                    v___x_2982_,
                                    v___x_2983_,
                                    v___x_2974_,
                                );
                            v___y_2962_ = v___x_2984_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2963_ = lean_array_get_size(v___y_2962_);
                v___x_2964_ = l_Std_Http_Headers_getAll___redArg___closed__9;
                v___x_2965_ = lean_nat_dec_lt(v___x_2960_, v___x_2963_);
                if v___x_2965_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2962_);
                    return v___x_2959_;
                } else {
                    v___x_2966_ = lean_nat_dec_le(v___x_2963_, v___x_2963_);
                    if v___x_2966_ == 0 {
                        if v___x_2965_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_2962_);
                            return v___x_2959_;
                        } else {
                            v___x_2967_ = 0usize;
                            v___x_2968_ = lean_usize_of_nat(v___x_2963_);
                            v___x_2969_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_2964_,
                                    v___f_2958_,
                                    v___y_2962_,
                                    v___x_2967_,
                                    v___x_2968_,
                                    v___x_2959_,
                                );
                            return v___x_2969_;
                        }
                    } else {
                        v___x_2970_ = 0usize;
                        v___x_2971_ = lean_usize_of_nat(v___x_2963_);
                        v___x_2972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2964_,
                            v___f_2958_,
                            v___y_2962_,
                            v___x_2970_,
                            v___x_2971_,
                            v___x_2959_,
                        );
                        return v___x_2972_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_size(
    mut v_headers_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_entries_2986_ = crate::leanh::lean_ctor_get(v_headers_2985_, 0);
    v___x_2987_ = lean_array_get_size(v_entries_2986_);
    return v___x_2987_;
}
pub unsafe fn l_Std_Http_Headers_size___boxed(
    mut v_headers_2988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2989_ = l_Std_Http_Headers_size(v_headers_2988_);
    crate::leanh::lean_dec_ref(v_headers_2988_);
    return v_res_2989_;
}
pub unsafe fn l_Std_Http_Headers_isEmpty(mut v_headers_2990_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_entries_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: u8 = 0;
    v_entries_2991_ = crate::leanh::lean_ctor_get(v_headers_2990_, 0);
    v___x_2992_ = lean_array_get_size(v_entries_2991_);
    v___x_2993_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2994_ = lean_nat_dec_eq(v___x_2992_, v___x_2993_);
    return v___x_2994_;
}
pub unsafe fn l_Std_Http_Headers_isEmpty___boxed(
    mut v_headers_2995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2996_: u8 = 0;
    let mut v_r_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2996_ = l_Std_Http_Headers_isEmpty(v_headers_2995_);
    crate::leanh::lean_dec_ref(v_headers_2995_);
    v_r_2997_ = crate::leanh::lean_box((v_res_2996_) as usize);
    return v_r_2997_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(
    mut v_as_2998_: *mut crate::leanh::LeanObject,
    mut v_i_2999_: usize,
    mut v_stop_3000_: usize,
    mut v_b_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3002_: u8 = 0;
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v_i_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: usize = 0;
    let mut v___x_3016_: usize = 0;
    let mut v_reuseFailAlloc_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3002_ = lean_usize_dec_eq(v_i_2999_, v_stop_3000_);
                if v___x_3002_ == 0 {
                    v___x_3003_ = lean_array_uget_borrowed(v_as_2998_, v_i_2999_);
                    v_fst_3004_ = crate::leanh::lean_ctor_get(v___x_3003_, 0);
                    v_entries_3005_ = crate::leanh::lean_ctor_get(v_b_3001_, 0);
                    v_indexes_3006_ = crate::leanh::lean_ctor_get(v_b_3001_, 1);
                    v_isSharedCheck_3019_ = (!crate::leanh::lean_is_exclusive(v_b_3001_)) as u8;
                    if v_isSharedCheck_3019_ == 0 {
                        v___x_3008_ = v_b_3001_;
                        v_isShared_3009_ = v_isSharedCheck_3019_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_indexes_3006_);
                        crate::leanh::lean_inc(v_entries_3005_);
                        crate::leanh::lean_dec(v_b_3001_);
                        v___x_3008_ = crate::leanh::lean_box(0);
                        v_isShared_3009_ = v_isSharedCheck_3019_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3001_;
                }
            }
            1 => {
                v_i_3010_ = lean_array_get_size(v_entries_3005_);
                crate::leanh::lean_inc(v___x_3003_);
                v_entries_3011_ = lean_array_push(v_entries_3005_, v___x_3003_);
                crate::leanh::lean_inc(v_fst_3004_);
                v_indexes_3012_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_3010_, v_indexes_3006_, v_fst_3004_);
                if v_isShared_3009_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3008_, 1, v_indexes_3012_);
                    crate::leanh::lean_ctor_set(v___x_3008_, 0, v_entries_3011_);
                    v___x_3014_ = v___x_3008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_entries_3011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_indexes_3012_);
                    v___x_3014_ = v_reuseFailAlloc_3018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3015_ = 1usize;
                v___x_3016_ = lean_usize_add(v_i_2999_, v___x_3015_);
                v_i_2999_ = v___x_3016_;
                v_b_3001_ = v___x_3014_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___boxed(
    mut v_as_3020_: *mut crate::leanh::LeanObject,
    mut v_i_3021_: *mut crate::leanh::LeanObject,
    mut v_stop_3022_: *mut crate::leanh::LeanObject,
    mut v_b_3023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3024_: usize = 0;
    let mut v_stop_boxed_3025_: usize = 0;
    let mut v_res_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3024_ = crate::leanh::lean_unbox_usize(v_i_3021_);
    crate::leanh::lean_dec(v_i_3021_);
    v_stop_boxed_3025_ = crate::leanh::lean_unbox_usize(v_stop_3022_);
    crate::leanh::lean_dec(v_stop_3022_);
    v_res_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_3020_, v_i_boxed_3024_, v_stop_boxed_3025_, v_b_3023_);
    crate::leanh::lean_dec_ref(v_as_3020_);
    return v_res_3026_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(
    mut v_m1_3027_: *mut crate::leanh::LeanObject,
    mut v_m2_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    v_entries_3029_ = crate::leanh::lean_ctor_get(v_m2_3028_, 0);
    v___x_3030_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3031_ = lean_array_get_size(v_entries_3029_);
    v___x_3032_ = lean_nat_dec_lt(v___x_3030_, v___x_3031_);
    if v___x_3032_ == 0 {
        return v_m1_3027_;
    } else {
        let mut v___x_3033_: u8 = 0;
        v___x_3033_ = lean_nat_dec_le(v___x_3031_, v___x_3031_);
        if v___x_3033_ == 0 {
            if v___x_3032_ == 0 {
                return v_m1_3027_;
            } else {
                let mut v___x_3034_: usize = 0;
                let mut v___x_3035_: usize = 0;
                let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3034_ = 0usize;
                v___x_3035_ = lean_usize_of_nat(v___x_3031_);
                v___x_3036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_3029_, v___x_3034_, v___x_3035_, v_m1_3027_);
                return v___x_3036_;
            }
        } else {
            let mut v___x_3037_: usize = 0;
            let mut v___x_3038_: usize = 0;
            let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3037_ = 0usize;
            v___x_3038_ = lean_usize_of_nat(v___x_3031_);
            v___x_3039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_3029_, v___x_3037_, v___x_3038_, v_m1_3027_);
            return v___x_3039_;
        }
    }
}
pub unsafe fn l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg___boxed(
    mut v_m1_3040_: *mut crate::leanh::LeanObject,
    mut v_m2_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ =
        l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(
            v_m1_3040_, v_m2_3041_,
        );
    crate::leanh::lean_dec_ref(v_m2_3041_);
    return v_res_3042_;
}
pub unsafe fn l_Std_Http_Headers_merge(
    mut v_headers1_3043_: *mut crate::leanh::LeanObject,
    mut v_headers2_3044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3045_ =
        l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(
            v_headers1_3043_,
            v_headers2_3044_,
        );
    return v___x_3045_;
}
pub unsafe fn l_Std_Http_Headers_merge___boxed(
    mut v_headers1_3046_: *mut crate::leanh::LeanObject,
    mut v_headers2_3047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3048_ = l_Std_Http_Headers_merge(v_headers1_3046_, v_headers2_3047_);
    crate::leanh::lean_dec_ref(v_headers2_3047_);
    return v_res_3048_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(
    mut v_00_u03b2_3049_: *mut crate::leanh::LeanObject,
    mut v_inst_3050_: *mut crate::leanh::LeanObject,
    mut v_inst_3051_: *mut crate::leanh::LeanObject,
    mut v_m1_3052_: *mut crate::leanh::LeanObject,
    mut v_m2_3053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3054_ =
        l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(
            v_m1_3052_, v_m2_3053_,
        );
    return v___x_3054_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___boxed(
    mut v_00_u03b2_3055_: *mut crate::leanh::LeanObject,
    mut v_inst_3056_: *mut crate::leanh::LeanObject,
    mut v_inst_3057_: *mut crate::leanh::LeanObject,
    mut v_m1_3058_: *mut crate::leanh::LeanObject,
    mut v_m2_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3060_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(
        v_00_u03b2_3055_,
        v_inst_3056_,
        v_inst_3057_,
        v_m1_3058_,
        v_m2_3059_,
    );
    crate::leanh::lean_dec_ref(v_m2_3059_);
    return v_res_3060_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(
    mut v_00_u03b2_3061_: *mut crate::leanh::LeanObject,
    mut v_as_3062_: *mut crate::leanh::LeanObject,
    mut v_i_3063_: usize,
    mut v_stop_3064_: usize,
    mut v_b_3065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_3062_, v_i_3063_, v_stop_3064_, v_b_3065_);
    return v___x_3066_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___boxed(
    mut v_00_u03b2_3067_: *mut crate::leanh::LeanObject,
    mut v_as_3068_: *mut crate::leanh::LeanObject,
    mut v_i_3069_: *mut crate::leanh::LeanObject,
    mut v_stop_3070_: *mut crate::leanh::LeanObject,
    mut v_b_3071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3072_: usize = 0;
    let mut v_stop_boxed_3073_: usize = 0;
    let mut v_res_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3072_ = crate::leanh::lean_unbox_usize(v_i_3069_);
    crate::leanh::lean_dec(v_i_3069_);
    v_stop_boxed_3073_ = crate::leanh::lean_unbox_usize(v_stop_3070_);
    crate::leanh::lean_dec(v_stop_3070_);
    v_res_3074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(v_00_u03b2_3067_, v_as_3068_, v_i_boxed_3072_, v_stop_boxed_3073_, v_b_3071_);
    crate::leanh::lean_dec_ref(v_as_3068_);
    return v_res_3074_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(
    mut v_map_3075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_entries_3076_ = crate::leanh::lean_ctor_get(v_map_3075_, 0);
    crate::leanh::lean_inc_ref(v_entries_3076_);
    crate::leanh::lean_dec_ref(v_map_3075_);
    v___x_3077_ = lean_array_to_list(v_entries_3076_);
    return v___x_3077_;
}
pub unsafe fn l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0(
    mut v_00_u03b2_3078_: *mut crate::leanh::LeanObject,
    mut v_map_3079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3080_ =
        l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(
            v_map_3079_,
        );
    return v___x_3080_;
}
pub unsafe fn l_Std_Http_Headers_toList(
    mut v_headers_3081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3082_ =
        l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(
            v_headers_3081_,
        );
    return v___x_3082_;
}
pub unsafe fn l_Std_Http_Headers_toArray(
    mut v_headers_3083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_entries_3084_ = crate::leanh::lean_ctor_get(v_headers_3083_, 0);
    crate::leanh::lean_inc_ref(v_entries_3084_);
    return v_entries_3084_;
}
pub unsafe fn l_Std_Http_Headers_toArray___boxed(
    mut v_headers_3085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3086_ = l_Std_Http_Headers_toArray(v_headers_3085_);
    crate::leanh::lean_dec_ref(v_headers_3085_);
    return v_res_3086_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(
    mut v_f_3087_: *mut crate::leanh::LeanObject,
    mut v_as_3088_: *mut crate::leanh::LeanObject,
    mut v_i_3089_: usize,
    mut v_stop_3090_: usize,
    mut v_b_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3092_: u8 = 0;
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: usize = 0;
    let mut v___x_3098_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3092_ = lean_usize_dec_eq(v_i_3089_, v_stop_3090_);
                if v___x_3092_ == 0 {
                    v___x_3093_ = lean_array_uget_borrowed(v_as_3088_, v_i_3089_);
                    v_fst_3094_ = crate::leanh::lean_ctor_get(v___x_3093_, 0);
                    v_snd_3095_ = crate::leanh::lean_ctor_get(v___x_3093_, 1);
                    crate::leanh::lean_inc(v_f_3087_);
                    crate::leanh::lean_inc(v_snd_3095_);
                    crate::leanh::lean_inc(v_fst_3094_);
                    v___x_3096_ =
                        crate::leanh::lean_apply_3(v_f_3087_, v_b_3091_, v_fst_3094_, v_snd_3095_);
                    v___x_3097_ = 1usize;
                    v___x_3098_ = lean_usize_add(v_i_3089_, v___x_3097_);
                    v_i_3089_ = v___x_3098_;
                    v_b_3091_ = v___x_3096_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_f_3087_);
                    return v_b_3091_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(
    mut v_f_3100_: *mut crate::leanh::LeanObject,
    mut v_as_3101_: *mut crate::leanh::LeanObject,
    mut v_i_3102_: *mut crate::leanh::LeanObject,
    mut v_stop_3103_: *mut crate::leanh::LeanObject,
    mut v_b_3104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3105_: usize = 0;
    let mut v_stop_boxed_3106_: usize = 0;
    let mut v_res_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3105_ = crate::leanh::lean_unbox_usize(v_i_3102_);
    crate::leanh::lean_dec(v_i_3102_);
    v_stop_boxed_3106_ = crate::leanh::lean_unbox_usize(v_stop_3103_);
    crate::leanh::lean_dec(v_stop_3103_);
    v_res_3107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_3100_, v_as_3101_, v_i_boxed_3105_, v_stop_boxed_3106_, v_b_3104_);
    crate::leanh::lean_dec_ref(v_as_3101_);
    return v_res_3107_;
}
pub unsafe fn l_Std_Http_Headers_fold___redArg(
    mut v_headers_3108_: *mut crate::leanh::LeanObject,
    mut v_init_3109_: *mut crate::leanh::LeanObject,
    mut v_f_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u8 = 0;
    v_entries_3111_ = crate::leanh::lean_ctor_get(v_headers_3108_, 0);
    v___x_3112_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3113_ = lean_array_get_size(v_entries_3111_);
    v___x_3114_ = lean_nat_dec_lt(v___x_3112_, v___x_3113_);
    if v___x_3114_ == 0 {
        crate::leanh::lean_dec(v_f_3110_);
        return v_init_3109_;
    } else {
        let mut v___x_3115_: u8 = 0;
        v___x_3115_ = lean_nat_dec_le(v___x_3113_, v___x_3113_);
        if v___x_3115_ == 0 {
            if v___x_3114_ == 0 {
                crate::leanh::lean_dec(v_f_3110_);
                return v_init_3109_;
            } else {
                let mut v___x_3116_: usize = 0;
                let mut v___x_3117_: usize = 0;
                let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3116_ = 0usize;
                v___x_3117_ = lean_usize_of_nat(v___x_3113_);
                v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_3110_, v_entries_3111_, v___x_3116_, v___x_3117_, v_init_3109_);
                return v___x_3118_;
            }
        } else {
            let mut v___x_3119_: usize = 0;
            let mut v___x_3120_: usize = 0;
            let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3119_ = 0usize;
            v___x_3120_ = lean_usize_of_nat(v___x_3113_);
            v___x_3121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_3110_, v_entries_3111_, v___x_3119_, v___x_3120_, v_init_3109_);
            return v___x_3121_;
        }
    }
}
pub unsafe fn l_Std_Http_Headers_fold___redArg___boxed(
    mut v_headers_3122_: *mut crate::leanh::LeanObject,
    mut v_init_3123_: *mut crate::leanh::LeanObject,
    mut v_f_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3125_ = l_Std_Http_Headers_fold___redArg(v_headers_3122_, v_init_3123_, v_f_3124_);
    crate::leanh::lean_dec_ref(v_headers_3122_);
    return v_res_3125_;
}
pub unsafe fn l_Std_Http_Headers_fold(
    mut v_00_u03b1_3126_: *mut crate::leanh::LeanObject,
    mut v_headers_3127_: *mut crate::leanh::LeanObject,
    mut v_init_3128_: *mut crate::leanh::LeanObject,
    mut v_f_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3130_ = l_Std_Http_Headers_fold___redArg(v_headers_3127_, v_init_3128_, v_f_3129_);
    return v___x_3130_;
}
pub unsafe fn l_Std_Http_Headers_fold___boxed(
    mut v_00_u03b1_3131_: *mut crate::leanh::LeanObject,
    mut v_headers_3132_: *mut crate::leanh::LeanObject,
    mut v_init_3133_: *mut crate::leanh::LeanObject,
    mut v_f_3134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3135_ =
        l_Std_Http_Headers_fold(v_00_u03b1_3131_, v_headers_3132_, v_init_3133_, v_f_3134_);
    crate::leanh::lean_dec_ref(v_headers_3132_);
    return v_res_3135_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(
    mut v_00_u03b1_3136_: *mut crate::leanh::LeanObject,
    mut v_f_3137_: *mut crate::leanh::LeanObject,
    mut v_as_3138_: *mut crate::leanh::LeanObject,
    mut v_i_3139_: usize,
    mut v_stop_3140_: usize,
    mut v_b_3141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_3137_, v_as_3138_, v_i_3139_, v_stop_3140_, v_b_3141_);
    return v___x_3142_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(
    mut v_00_u03b1_3143_: *mut crate::leanh::LeanObject,
    mut v_f_3144_: *mut crate::leanh::LeanObject,
    mut v_as_3145_: *mut crate::leanh::LeanObject,
    mut v_i_3146_: *mut crate::leanh::LeanObject,
    mut v_stop_3147_: *mut crate::leanh::LeanObject,
    mut v_b_3148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3149_: usize = 0;
    let mut v_stop_boxed_3150_: usize = 0;
    let mut v_res_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3149_ = crate::leanh::lean_unbox_usize(v_i_3146_);
    crate::leanh::lean_dec(v_i_3146_);
    v_stop_boxed_3150_ = crate::leanh::lean_unbox_usize(v_stop_3147_);
    crate::leanh::lean_dec(v_stop_3147_);
    v_res_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(v_00_u03b1_3143_, v_f_3144_, v_as_3145_, v_i_boxed_3149_, v_stop_boxed_3150_, v_b_3148_);
    crate::leanh::lean_dec_ref(v_as_3145_);
    return v_res_3151_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(
    mut v_f_3152_: *mut crate::leanh::LeanObject,
    mut v_sz_3153_: usize,
    mut v_i_3154_: usize,
    mut v_bs_3155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3156_: u8 = 0;
    let mut v_v_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3162_: u8 = 0;
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: usize = 0;
    let mut v___x_3169_: usize = 0;
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3156_ = lean_usize_dec_lt(v_i_3154_, v_sz_3153_);
                if v___x_3156_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_3152_);
                    return v_bs_3155_;
                } else {
                    v_v_3157_ = lean_array_uget(v_bs_3155_, v_i_3154_);
                    v_fst_3158_ = crate::leanh::lean_ctor_get(v_v_3157_, 0);
                    v_snd_3159_ = crate::leanh::lean_ctor_get(v_v_3157_, 1);
                    v_isSharedCheck_3173_ = (!crate::leanh::lean_is_exclusive(v_v_3157_)) as u8;
                    if v_isSharedCheck_3173_ == 0 {
                        v___x_3161_ = v_v_3157_;
                        v_isShared_3162_ = v_isSharedCheck_3173_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3159_);
                        crate::leanh::lean_inc(v_fst_3158_);
                        crate::leanh::lean_dec(v_v_3157_);
                        v___x_3161_ = crate::leanh::lean_box(0);
                        v_isShared_3162_ = v_isSharedCheck_3173_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3163_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3164_ = lean_array_uset(v_bs_3155_, v_i_3154_, v___x_3163_);
                crate::leanh::lean_inc_ref(v_f_3152_);
                crate::leanh::lean_inc(v_fst_3158_);
                v___x_3165_ = crate::leanh::lean_apply_2(v_f_3152_, v_fst_3158_, v_snd_3159_);
                if v_isShared_3162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3161_, 1, v___x_3165_);
                    v___x_3167_ = v___x_3161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3172_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_fst_3158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 1, v___x_3165_);
                    v___x_3167_ = v_reuseFailAlloc_3172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3168_ = 1usize;
                v___x_3169_ = lean_usize_add(v_i_3154_, v___x_3168_);
                v___x_3170_ = lean_array_uset(v_bs_x27_3164_, v_i_3154_, v___x_3167_);
                v_i_3154_ = v___x_3169_;
                v_bs_3155_ = v___x_3170_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(
    mut v_f_3174_: *mut crate::leanh::LeanObject,
    mut v_sz_3175_: *mut crate::leanh::LeanObject,
    mut v_i_3176_: *mut crate::leanh::LeanObject,
    mut v_bs_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3178_: usize = 0;
    let mut v_i_boxed_3179_: usize = 0;
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3178_ = crate::leanh::lean_unbox_usize(v_sz_3175_);
    crate::leanh::lean_dec(v_sz_3175_);
    v_i_boxed_3179_ = crate::leanh::lean_unbox_usize(v_i_3176_);
    crate::leanh::lean_dec(v_i_3176_);
    v_res_3180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_3174_, v_sz_boxed_3178_, v_i_boxed_3179_, v_bs_3177_);
    return v_res_3180_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(
    mut v_as_3181_: *mut crate::leanh::LeanObject,
    mut v_i_3182_: usize,
    mut v_stop_3183_: usize,
    mut v_b_3184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3185_: u8 = 0;
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3192_: u8 = 0;
    let mut v_i_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: usize = 0;
    let mut v_reuseFailAlloc_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3185_ = lean_usize_dec_eq(v_i_3182_, v_stop_3183_);
                if v___x_3185_ == 0 {
                    v___x_3186_ = lean_array_uget_borrowed(v_as_3181_, v_i_3182_);
                    v_fst_3187_ = crate::leanh::lean_ctor_get(v___x_3186_, 0);
                    v_entries_3188_ = crate::leanh::lean_ctor_get(v_b_3184_, 0);
                    v_indexes_3189_ = crate::leanh::lean_ctor_get(v_b_3184_, 1);
                    v_isSharedCheck_3202_ = (!crate::leanh::lean_is_exclusive(v_b_3184_)) as u8;
                    if v_isSharedCheck_3202_ == 0 {
                        v___x_3191_ = v_b_3184_;
                        v_isShared_3192_ = v_isSharedCheck_3202_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_indexes_3189_);
                        crate::leanh::lean_inc(v_entries_3188_);
                        crate::leanh::lean_dec(v_b_3184_);
                        v___x_3191_ = crate::leanh::lean_box(0);
                        v_isShared_3192_ = v_isSharedCheck_3202_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3184_;
                }
            }
            1 => {
                v_i_3193_ = lean_array_get_size(v_entries_3188_);
                crate::leanh::lean_inc(v___x_3186_);
                v_entries_3194_ = lean_array_push(v_entries_3188_, v___x_3186_);
                crate::leanh::lean_inc(v_fst_3187_);
                v_indexes_3195_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_3193_, v_indexes_3189_, v_fst_3187_);
                if v_isShared_3192_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3191_, 1, v_indexes_3195_);
                    crate::leanh::lean_ctor_set(v___x_3191_, 0, v_entries_3194_);
                    v___x_3197_ = v___x_3191_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_entries_3194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_indexes_3195_);
                    v___x_3197_ = v_reuseFailAlloc_3201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3198_ = 1usize;
                v___x_3199_ = lean_usize_add(v_i_3182_, v___x_3198_);
                v_i_3182_ = v___x_3199_;
                v_b_3184_ = v___x_3197_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(
    mut v_as_3203_: *mut crate::leanh::LeanObject,
    mut v_i_3204_: *mut crate::leanh::LeanObject,
    mut v_stop_3205_: *mut crate::leanh::LeanObject,
    mut v_b_3206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3207_: usize = 0;
    let mut v_stop_boxed_3208_: usize = 0;
    let mut v_res_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3207_ = crate::leanh::lean_unbox_usize(v_i_3204_);
    crate::leanh::lean_dec(v_i_3204_);
    v_stop_boxed_3208_ = crate::leanh::lean_unbox_usize(v_stop_3205_);
    crate::leanh::lean_dec(v_stop_3205_);
    v_res_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_as_3203_, v_i_boxed_3207_, v_stop_boxed_3208_, v_b_3206_);
    crate::leanh::lean_dec_ref(v_as_3203_);
    return v_res_3209_;
}
pub unsafe fn l_Std_Http_Headers_mapValues(
    mut v_headers_3210_: *mut crate::leanh::LeanObject,
    mut v_f_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3213_: usize = 0;
    let mut v___x_3214_: usize = 0;
    let mut v_pairs_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: u8 = 0;
    v_entries_3212_ = crate::leanh::lean_ctor_get(v_headers_3210_, 0);
    crate::leanh::lean_inc_ref(v_entries_3212_);
    crate::leanh::lean_dec_ref(v_headers_3210_);
    v_sz_3213_ = lean_array_size(v_entries_3212_);
    v___x_3214_ = 0usize;
    v_pairs_3215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_3211_, v_sz_3213_, v___x_3214_, v_entries_3212_);
    v___x_3216_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0_once),
        _init_l_Std_Http_Headers_empty___closed__0,
    );
    v___x_3217_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3218_ = lean_array_get_size(v_pairs_3215_);
    v___x_3219_ = lean_nat_dec_lt(v___x_3217_, v___x_3218_);
    if v___x_3219_ == 0 {
        crate::leanh::lean_dec_ref(v_pairs_3215_);
        return v___x_3216_;
    } else {
        let mut v___x_3220_: u8 = 0;
        v___x_3220_ = lean_nat_dec_le(v___x_3218_, v___x_3218_);
        if v___x_3220_ == 0 {
            if v___x_3219_ == 0 {
                crate::leanh::lean_dec_ref(v_pairs_3215_);
                return v___x_3216_;
            } else {
                let mut v___x_3221_: usize = 0;
                let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3221_ = lean_usize_of_nat(v___x_3218_);
                v___x_3222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_3215_, v___x_3214_, v___x_3221_, v___x_3216_);
                crate::leanh::lean_dec_ref(v_pairs_3215_);
                return v___x_3222_;
            }
        } else {
            let mut v___x_3223_: usize = 0;
            let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3223_ = lean_usize_of_nat(v___x_3218_);
            v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_3215_, v___x_3214_, v___x_3223_, v___x_3216_);
            crate::leanh::lean_dec_ref(v_pairs_3215_);
            return v___x_3224_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(
    mut v_f_3225_: *mut crate::leanh::LeanObject,
    mut v_as_3226_: *mut crate::leanh::LeanObject,
    mut v_i_3227_: usize,
    mut v_stop_3228_: usize,
    mut v_b_3229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: usize = 0;
    let mut v___x_3235_: u8 = 0;
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3241_: u8 = 0;
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3235_ = lean_usize_dec_eq(v_i_3227_, v_stop_3228_);
                if v___x_3235_ == 0 {
                    v___x_3236_ = lean_array_uget(v_as_3226_, v_i_3227_);
                    v_fst_3237_ = crate::leanh::lean_ctor_get(v___x_3236_, 0);
                    v_snd_3238_ = crate::leanh::lean_ctor_get(v___x_3236_, 1);
                    v_isSharedCheck_3248_ = (!crate::leanh::lean_is_exclusive(v___x_3236_)) as u8;
                    if v_isSharedCheck_3248_ == 0 {
                        v___x_3240_ = v___x_3236_;
                        v_isShared_3241_ = v_isSharedCheck_3248_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3238_);
                        crate::leanh::lean_inc(v_fst_3237_);
                        crate::leanh::lean_dec(v___x_3236_);
                        v___x_3240_ = crate::leanh::lean_box(0);
                        v_isShared_3241_ = v_isSharedCheck_3248_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_3225_);
                    return v_b_3229_;
                }
            }
            1 => {
                v___x_3232_ = 1usize;
                v___x_3233_ = lean_usize_add(v_i_3227_, v___x_3232_);
                v_i_3227_ = v___x_3233_;
                v_b_3229_ = v___y_3231_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_f_3225_);
                crate::leanh::lean_inc(v_fst_3237_);
                v___x_3242_ = crate::leanh::lean_apply_2(v_f_3225_, v_fst_3237_, v_snd_3238_);
                if crate::leanh::lean_obj_tag(v___x_3242_) == 0 {
                    crate::leanh::lean_del_object(v___x_3240_);
                    crate::leanh::lean_dec(v_fst_3237_);
                    v___y_3231_ = v_b_3229_;
                    state = 1;
                    continue;
                } else {
                    v_val_3243_ = crate::leanh::lean_ctor_get(v___x_3242_, 0);
                    crate::leanh::lean_inc(v_val_3243_);
                    crate::leanh::lean_dec_ref_known(v___x_3242_, 1);
                    if v_isShared_3241_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3240_, 1, v_val_3243_);
                        v___x_3245_ = v___x_3240_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3247_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_fst_3237_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_val_3243_);
                        v___x_3245_ = v_reuseFailAlloc_3247_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3246_ = lean_array_push(v_b_3229_, v___x_3245_);
                v___y_3231_ = v___x_3246_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(
    mut v_f_3249_: *mut crate::leanh::LeanObject,
    mut v_as_3250_: *mut crate::leanh::LeanObject,
    mut v_i_3251_: *mut crate::leanh::LeanObject,
    mut v_stop_3252_: *mut crate::leanh::LeanObject,
    mut v_b_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3254_: usize = 0;
    let mut v_stop_boxed_3255_: usize = 0;
    let mut v_res_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3254_ = crate::leanh::lean_unbox_usize(v_i_3251_);
    crate::leanh::lean_dec(v_i_3251_);
    v_stop_boxed_3255_ = crate::leanh::lean_unbox_usize(v_stop_3252_);
    crate::leanh::lean_dec(v_stop_3252_);
    v_res_3256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_3249_, v_as_3250_, v_i_boxed_3254_, v_stop_boxed_3255_, v_b_3253_);
    crate::leanh::lean_dec_ref(v_as_3250_);
    return v_res_3256_;
}
pub unsafe fn l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(
    mut v_f_3257_: *mut crate::leanh::LeanObject,
    mut v_as_3258_: *mut crate::leanh::LeanObject,
    mut v_start_3259_: *mut crate::leanh::LeanObject,
    mut v_stop_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    v___x_3261_ = l_Std_Http_instInhabitedHeaders_default___closed__0;
    v___x_3262_ = lean_nat_dec_lt(v_start_3259_, v_stop_3260_);
    if v___x_3262_ == 0 {
        crate::leanh::lean_dec_ref(v_f_3257_);
        return v___x_3261_;
    } else {
        let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3264_: u8 = 0;
        v___x_3263_ = lean_array_get_size(v_as_3258_);
        v___x_3264_ = lean_nat_dec_le(v_stop_3260_, v___x_3263_);
        if v___x_3264_ == 0 {
            let mut v___x_3265_: u8 = 0;
            v___x_3265_ = lean_nat_dec_lt(v_start_3259_, v___x_3263_);
            if v___x_3265_ == 0 {
                crate::leanh::lean_dec_ref(v_f_3257_);
                return v___x_3261_;
            } else {
                let mut v___x_3266_: usize = 0;
                let mut v___x_3267_: usize = 0;
                let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3266_ = lean_usize_of_nat(v_start_3259_);
                v___x_3267_ = lean_usize_of_nat(v___x_3263_);
                v___x_3268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_3257_, v_as_3258_, v___x_3266_, v___x_3267_, v___x_3261_);
                return v___x_3268_;
            }
        } else {
            let mut v___x_3269_: usize = 0;
            let mut v___x_3270_: usize = 0;
            let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3269_ = lean_usize_of_nat(v_start_3259_);
            v___x_3270_ = lean_usize_of_nat(v_stop_3260_);
            v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_3257_, v_as_3258_, v___x_3269_, v___x_3270_, v___x_3261_);
            return v___x_3271_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(
    mut v_f_3272_: *mut crate::leanh::LeanObject,
    mut v_as_3273_: *mut crate::leanh::LeanObject,
    mut v_start_3274_: *mut crate::leanh::LeanObject,
    mut v_stop_3275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3276_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(
        v_f_3272_,
        v_as_3273_,
        v_start_3274_,
        v_stop_3275_,
    );
    crate::leanh::lean_dec(v_stop_3275_);
    crate::leanh::lean_dec(v_start_3274_);
    crate::leanh::lean_dec_ref(v_as_3273_);
    return v_res_3276_;
}
pub unsafe fn l_Std_Http_Headers_filterMap(
    mut v_headers_3277_: *mut crate::leanh::LeanObject,
    mut v_f_3278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pairs_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    v_entries_3279_ = crate::leanh::lean_ctor_get(v_headers_3277_, 0);
    v___x_3280_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3281_ = lean_array_get_size(v_entries_3279_);
    v_pairs_3282_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(
        v_f_3278_,
        v_entries_3279_,
        v___x_3280_,
        v___x_3281_,
    );
    v___x_3283_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0_once),
        _init_l_Std_Http_Headers_empty___closed__0,
    );
    v___x_3284_ = lean_array_get_size(v_pairs_3282_);
    v___x_3285_ = lean_nat_dec_lt(v___x_3280_, v___x_3284_);
    if v___x_3285_ == 0 {
        crate::leanh::lean_dec_ref(v_pairs_3282_);
        return v___x_3283_;
    } else {
        let mut v___x_3286_: u8 = 0;
        v___x_3286_ = lean_nat_dec_le(v___x_3284_, v___x_3284_);
        if v___x_3286_ == 0 {
            if v___x_3285_ == 0 {
                crate::leanh::lean_dec_ref(v_pairs_3282_);
                return v___x_3283_;
            } else {
                let mut v___x_3287_: usize = 0;
                let mut v___x_3288_: usize = 0;
                let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3287_ = 0usize;
                v___x_3288_ = lean_usize_of_nat(v___x_3284_);
                v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_3282_, v___x_3287_, v___x_3288_, v___x_3283_);
                crate::leanh::lean_dec_ref(v_pairs_3282_);
                return v___x_3289_;
            }
        } else {
            let mut v___x_3290_: usize = 0;
            let mut v___x_3291_: usize = 0;
            let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3290_ = 0usize;
            v___x_3291_ = lean_usize_of_nat(v___x_3284_);
            v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_3282_, v___x_3290_, v___x_3291_, v___x_3283_);
            crate::leanh::lean_dec_ref(v_pairs_3282_);
            return v___x_3292_;
        }
    }
}
pub unsafe fn l_Std_Http_Headers_filterMap___boxed(
    mut v_headers_3293_: *mut crate::leanh::LeanObject,
    mut v_f_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3295_ = l_Std_Http_Headers_filterMap(v_headers_3293_, v_f_3294_);
    crate::leanh::lean_dec_ref(v_headers_3293_);
    return v_res_3295_;
}
pub unsafe fn l_Std_Http_Headers_filter___lam__0(
    mut v_f_3296_: *mut crate::leanh::LeanObject,
    mut v_k_3297_: *mut crate::leanh::LeanObject,
    mut v_v_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: u8 = 0;
    crate::leanh::lean_inc_ref(v_v_3298_);
    v___x_3299_ = crate::leanh::lean_apply_2(v_f_3296_, v_k_3297_, v_v_3298_);
    v___x_3300_ = (crate::leanh::lean_unbox(v___x_3299_) as u8);
    if v___x_3300_ == 0 {
        let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_v_3298_);
        v___x_3301_ = crate::leanh::lean_box(0);
        return v___x_3301_;
    } else {
        let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3302_, 0, v_v_3298_);
        return v___x_3302_;
    }
}
pub unsafe fn l_Std_Http_Headers_filter(
    mut v_headers_3303_: *mut crate::leanh::LeanObject,
    mut v_f_3304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3305_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Headers_filter___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3305_, 0, v_f_3304_);
    v___x_3306_ = l_Std_Http_Headers_filterMap(v_headers_3303_, v___f_3305_);
    return v___x_3306_;
}
pub unsafe fn l_Std_Http_Headers_filter___boxed(
    mut v_headers_3307_: *mut crate::leanh::LeanObject,
    mut v_f_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3309_ = l_Std_Http_Headers_filter(v_headers_3307_, v_f_3308_);
    crate::leanh::lean_dec_ref(v_headers_3307_);
    return v_res_3309_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(
    mut v_name_3310_: *mut crate::leanh::LeanObject,
    mut v_f_3311_: *mut crate::leanh::LeanObject,
    mut v_as_3312_: *mut crate::leanh::LeanObject,
    mut v_i_3313_: usize,
    mut v_stop_3314_: usize,
    mut v_b_3315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3322_: u8 = 0;
    let mut v___y_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3329_: u8 = 0;
    let mut v_i_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: usize = 0;
    let mut v___x_3338_: usize = 0;
    let mut v_reuseFailAlloc_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3342_: u8 = 0;
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3316_ = lean_usize_dec_eq(v_i_3313_, v_stop_3314_);
                if v___x_3316_ == 0 {
                    v___x_3317_ = lean_array_uget(v_as_3312_, v_i_3313_);
                    v_fst_3318_ = crate::leanh::lean_ctor_get(v___x_3317_, 0);
                    v_snd_3319_ = crate::leanh::lean_ctor_get(v___x_3317_, 1);
                    v_isSharedCheck_3345_ = (!crate::leanh::lean_is_exclusive(v___x_3317_)) as u8;
                    if v_isSharedCheck_3345_ == 0 {
                        v___x_3321_ = v___x_3317_;
                        v_isShared_3322_ = v_isSharedCheck_3345_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3319_);
                        crate::leanh::lean_inc(v_fst_3318_);
                        crate::leanh::lean_dec(v___x_3317_);
                        v___x_3321_ = crate::leanh::lean_box(0);
                        v_isShared_3322_ = v_isSharedCheck_3345_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_3311_);
                    return v_b_3315_;
                }
            }
            1 => {
                v___x_3343_ = lean_string_dec_eq(v_fst_3318_, v_name_3310_);
                if v___x_3343_ == 0 {
                    v___y_3324_ = v_snd_3319_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_3311_);
                    v___x_3344_ = crate::leanh::lean_apply_1(v_f_3311_, v_snd_3319_);
                    v___y_3324_ = v___x_3344_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_entries_3325_ = crate::leanh::lean_ctor_get(v_b_3315_, 0);
                v_indexes_3326_ = crate::leanh::lean_ctor_get(v_b_3315_, 1);
                v_isSharedCheck_3342_ = (!crate::leanh::lean_is_exclusive(v_b_3315_)) as u8;
                if v_isSharedCheck_3342_ == 0 {
                    v___x_3328_ = v_b_3315_;
                    v_isShared_3329_ = v_isSharedCheck_3342_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_3326_);
                    crate::leanh::lean_inc(v_entries_3325_);
                    crate::leanh::lean_dec(v_b_3315_);
                    v___x_3328_ = crate::leanh::lean_box(0);
                    v_isShared_3329_ = v_isSharedCheck_3342_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_i_3330_ = lean_array_get_size(v_entries_3325_);
                crate::leanh::lean_inc(v_fst_3318_);
                if v_isShared_3322_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3321_, 1, v___y_3324_);
                    v___x_3332_ = v___x_3321_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3341_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_fst_3318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 1, v___y_3324_);
                    v___x_3332_ = v_reuseFailAlloc_3341_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_3333_ = lean_array_push(v_entries_3325_, v___x_3332_);
                v_indexes_3334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_3330_, v_indexes_3326_, v_fst_3318_);
                if v_isShared_3329_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3328_, 1, v_indexes_3334_);
                    crate::leanh::lean_ctor_set(v___x_3328_, 0, v_entries_3333_);
                    v___x_3336_ = v___x_3328_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3340_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_entries_3333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_indexes_3334_);
                    v___x_3336_ = v_reuseFailAlloc_3340_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3337_ = 1usize;
                v___x_3338_ = lean_usize_add(v_i_3313_, v___x_3337_);
                v_i_3313_ = v___x_3338_;
                v_b_3315_ = v___x_3336_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0___boxed(
    mut v_name_3346_: *mut crate::leanh::LeanObject,
    mut v_f_3347_: *mut crate::leanh::LeanObject,
    mut v_as_3348_: *mut crate::leanh::LeanObject,
    mut v_i_3349_: *mut crate::leanh::LeanObject,
    mut v_stop_3350_: *mut crate::leanh::LeanObject,
    mut v_b_3351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3352_: usize = 0;
    let mut v_stop_boxed_3353_: usize = 0;
    let mut v_res_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3352_ = crate::leanh::lean_unbox_usize(v_i_3349_);
    crate::leanh::lean_dec(v_i_3349_);
    v_stop_boxed_3353_ = crate::leanh::lean_unbox_usize(v_stop_3350_);
    crate::leanh::lean_dec(v_stop_3350_);
    v_res_3354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_3346_, v_f_3347_, v_as_3348_, v_i_boxed_3352_, v_stop_boxed_3353_, v_b_3351_);
    crate::leanh::lean_dec_ref(v_as_3348_);
    crate::leanh::lean_dec_ref(v_name_3346_);
    return v_res_3354_;
}
pub unsafe fn l_Std_Http_Headers_update(
    mut v_headers_3355_: *mut crate::leanh::LeanObject,
    mut v_name_3356_: *mut crate::leanh::LeanObject,
    mut v_f_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    v___f_3358_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_3359_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    crate::leanh::lean_inc_ref(v_name_3356_);
    v___x_3360_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
        v___f_3358_,
        v___f_3359_,
        v_name_3356_,
        v_headers_3355_,
    );
    if v___x_3360_ == 0 {
        crate::leanh::lean_dec_ref(v_f_3357_);
        crate::leanh::lean_dec_ref(v_name_3356_);
        crate::leanh::lean_inc_ref(v_headers_3355_);
        return v_headers_3355_;
    } else {
        let mut v_entries_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3365_: u8 = 0;
        v_entries_3361_ = crate::leanh::lean_ctor_get(v_headers_3355_, 0);
        v___x_3362_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0),
            core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0_once),
            _init_l_Std_Http_Headers_empty___closed__0,
        );
        v___x_3363_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3364_ = lean_array_get_size(v_entries_3361_);
        v___x_3365_ = lean_nat_dec_lt(v___x_3363_, v___x_3364_);
        if v___x_3365_ == 0 {
            crate::leanh::lean_dec_ref(v_f_3357_);
            crate::leanh::lean_dec_ref(v_name_3356_);
            return v___x_3362_;
        } else {
            let mut v___x_3366_: u8 = 0;
            v___x_3366_ = lean_nat_dec_le(v___x_3364_, v___x_3364_);
            if v___x_3366_ == 0 {
                if v___x_3365_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_3357_);
                    crate::leanh::lean_dec_ref(v_name_3356_);
                    return v___x_3362_;
                } else {
                    let mut v___x_3367_: usize = 0;
                    let mut v___x_3368_: usize = 0;
                    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_3367_ = 0usize;
                    v___x_3368_ = lean_usize_of_nat(v___x_3364_);
                    v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_3356_, v_f_3357_, v_entries_3361_, v___x_3367_, v___x_3368_, v___x_3362_);
                    crate::leanh::lean_dec_ref(v_name_3356_);
                    return v___x_3369_;
                }
            } else {
                let mut v___x_3370_: usize = 0;
                let mut v___x_3371_: usize = 0;
                let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3370_ = 0usize;
                v___x_3371_ = lean_usize_of_nat(v___x_3364_);
                v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_3356_, v_f_3357_, v_entries_3361_, v___x_3370_, v___x_3371_, v___x_3362_);
                crate::leanh::lean_dec_ref(v_name_3356_);
                return v___x_3372_;
            }
        }
    }
}
pub unsafe fn l_Std_Http_Headers_update___boxed(
    mut v_headers_3373_: *mut crate::leanh::LeanObject,
    mut v_name_3374_: *mut crate::leanh::LeanObject,
    mut v_f_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3376_ = l_Std_Http_Headers_update(v_headers_3373_, v_name_3374_, v_f_3375_);
    crate::leanh::lean_dec_ref(v_headers_3373_);
    return v_res_3376_;
}
pub unsafe fn l_Std_Http_Headers_replaceLast(
    mut v_headers_3377_: *mut crate::leanh::LeanObject,
    mut v_name_3378_: *mut crate::leanh::LeanObject,
    mut v_value_3379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: u8 = 0;
    let mut v_entries_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3387_: u8 = 0;
    let mut v_idxs_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastIdx_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3380_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
                v___f_3381_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
                crate::leanh::lean_inc_ref(v_name_3378_);
                v___x_3382_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(
                    v___f_3380_,
                    v___f_3381_,
                    v_name_3378_,
                    v_headers_3377_,
                );
                if v___x_3382_ == 0 {
                    crate::leanh::lean_dec_ref(v_value_3379_);
                    crate::leanh::lean_dec_ref(v_name_3378_);
                    return v_headers_3377_;
                } else {
                    v_entries_3383_ = crate::leanh::lean_ctor_get(v_headers_3377_, 0);
                    v_indexes_3384_ = crate::leanh::lean_ctor_get(v_headers_3377_, 1);
                    v_isSharedCheck_3398_ =
                        (!crate::leanh::lean_is_exclusive(v_headers_3377_)) as u8;
                    if v_isSharedCheck_3398_ == 0 {
                        v___x_3386_ = v_headers_3377_;
                        v_isShared_3387_ = v_isSharedCheck_3398_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_indexes_3384_);
                        crate::leanh::lean_inc(v_entries_3383_);
                        crate::leanh::lean_dec(v_headers_3377_);
                        v___x_3386_ = crate::leanh::lean_box(0);
                        v_isShared_3387_ = v_isSharedCheck_3398_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_name_3378_);
                v_idxs_3388_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(
                    v___f_3380_,
                    v___f_3381_,
                    v_indexes_3384_,
                    v_name_3378_,
                );
                v___x_3389_ = lean_array_get_size(v_idxs_3388_);
                v___x_3390_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3391_ = lean_nat_sub(v___x_3389_, v___x_3390_);
                v_lastIdx_3392_ = lean_array_fget(v_idxs_3388_, v___x_3391_);
                crate::leanh::lean_dec(v___x_3391_);
                crate::leanh::lean_dec(v_idxs_3388_);
                v___x_3393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3393_, 0, v_name_3378_);
                crate::leanh::lean_ctor_set(v___x_3393_, 1, v_value_3379_);
                v_entries_3394_ = lean_array_fset(v_entries_3383_, v_lastIdx_3392_, v___x_3393_);
                crate::leanh::lean_dec(v_lastIdx_3392_);
                if v_isShared_3387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3386_, 0, v_entries_3394_);
                    v___x_3396_ = v___x_3386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3397_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_entries_3394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_indexes_3384_);
                    v___x_3396_ = v_reuseFailAlloc_3397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_instToString___lam__0(
    mut v___x_3399_: *mut crate::leanh::LeanObject,
    mut v___x_3400_: *mut crate::leanh::LeanObject,
    mut v___x_3401_: *mut crate::leanh::LeanObject,
    mut v_fst_3402_: *mut crate::leanh::LeanObject,
    mut v___x_3403_: *mut crate::leanh::LeanObject,
    mut v___x_3404_: u32,
    mut v___x_3405_: *mut crate::leanh::LeanObject,
    mut v_it_3406_: *mut crate::leanh::LeanObject,
    mut v_acc_3407_: *mut crate::leanh::LeanObject,
    mut v_hP_3408_: *mut crate::leanh::LeanObject,
    mut v_recur_3409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3418_: u8 = 0;
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3426_: u8 = 0;
    let mut v_it_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: u32 = 0;
    let mut v___x_3433_: u32 = 0;
    let mut v___x_3434_: u8 = 0;
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u32 = 0;
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: u32 = 0;
    let mut v___x_3440_: u32 = 0;
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3446_: u8 = 0;
    let mut v___x_3447_: u8 = 0;
    let mut v___x_3448_: u32 = 0;
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_it_3406_) == 0 {
                    v_currPos_3442_ = crate::leanh::lean_ctor_get(v_it_3406_, 0);
                    v_searcher_3443_ = crate::leanh::lean_ctor_get(v_it_3406_, 1);
                    v_isSharedCheck_3465_ = (!crate::leanh::lean_is_exclusive(v_it_3406_)) as u8;
                    if v_isSharedCheck_3465_ == 0 {
                        v___x_3445_ = v_it_3406_;
                        v_isShared_3446_ = v_isSharedCheck_3465_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_3443_);
                        crate::leanh::lean_inc(v_currPos_3442_);
                        crate::leanh::lean_dec(v_it_3406_);
                        v___x_3445_ = crate::leanh::lean_box(0);
                        v_isShared_3446_ = v_isSharedCheck_3465_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_recur_3409_);
                    crate::leanh::lean_dec(v___x_3403_);
                    return v_acc_3407_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_acc_3407_) == 0 {
                    v___x_3413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3413_, 0, v_out_3412_);
                    v___x_3414_ = crate::leanh::lean_apply_4(
                        v_recur_3409_,
                        v_it_3411_,
                        v___x_3413_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3414_;
                } else {
                    v_val_3415_ = crate::leanh::lean_ctor_get(v_acc_3407_, 0);
                    v_isSharedCheck_3426_ = (!crate::leanh::lean_is_exclusive(v_acc_3407_)) as u8;
                    if v_isSharedCheck_3426_ == 0 {
                        v___x_3417_ = v_acc_3407_;
                        v_isShared_3418_ = v_isSharedCheck_3426_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3415_);
                        crate::leanh::lean_dec(v_acc_3407_);
                        v___x_3417_ = crate::leanh::lean_box(0);
                        v_isShared_3418_ = v_isSharedCheck_3426_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3419_ = lean_string_utf8_extract(v___x_3399_, v___x_3400_, v___x_3401_);
                v___x_3420_ = lean_string_append(v_val_3415_, v___x_3419_);
                crate::leanh::lean_dec_ref(v___x_3419_);
                v___x_3421_ = lean_string_append(v___x_3420_, v_out_3412_);
                crate::leanh::lean_dec_ref(v_out_3412_);
                if v_isShared_3418_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3417_, 0, v___x_3421_);
                    v___x_3423_ = v___x_3417_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3421_);
                    v___x_3423_ = v_reuseFailAlloc_3425_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3424_ = crate::leanh::lean_apply_4(
                    v_recur_3409_,
                    v_it_3411_,
                    v___x_3423_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3424_;
            }
            4 => {
                v___x_3431_ = lean_string_utf8_extract(
                    v_fst_3402_,
                    v_startInclusive_3429_,
                    v_endExclusive_3430_,
                );
                crate::leanh::lean_dec(v_endExclusive_3430_);
                crate::leanh::lean_dec(v_startInclusive_3429_);
                v___x_3432_ = lean_string_utf8_get(v___x_3431_, v___x_3400_);
                v___x_3433_ = 97;
                v___x_3434_ = lean_uint32_dec_le(v___x_3433_, v___x_3432_);
                if v___x_3434_ == 0 {
                    v___x_3435_ = lean_string_utf8_set(v___x_3431_, v___x_3400_, v___x_3432_);
                    v_it_3411_ = v_it_3428_;
                    v_out_3412_ = v___x_3435_;
                    state = 1;
                    continue;
                } else {
                    v___x_3436_ = 122;
                    v___x_3437_ = lean_uint32_dec_le(v___x_3432_, v___x_3436_);
                    if v___x_3437_ == 0 {
                        v___x_3438_ = lean_string_utf8_set(v___x_3431_, v___x_3400_, v___x_3432_);
                        v_it_3411_ = v_it_3428_;
                        v_out_3412_ = v___x_3438_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3439_ = 4294967264;
                        v___x_3440_ = lean_uint32_add(v___x_3432_, v___x_3439_);
                        v___x_3441_ = lean_string_utf8_set(v___x_3431_, v___x_3400_, v___x_3440_);
                        v_it_3411_ = v_it_3428_;
                        v_out_3412_ = v___x_3441_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3447_ = lean_nat_dec_eq(v_searcher_3443_, v___x_3403_);
                if v___x_3447_ == 0 {
                    crate::leanh::lean_dec(v___x_3403_);
                    v___x_3448_ = lean_string_utf8_get_fast(v_fst_3402_, v_searcher_3443_);
                    v___x_3449_ = lean_uint32_dec_eq(v___x_3448_, v___x_3404_);
                    if v___x_3449_ == 0 {
                        v___x_3450_ = lean_string_utf8_next_fast(v_fst_3402_, v_searcher_3443_);
                        crate::leanh::lean_dec(v_searcher_3443_);
                        if v_isShared_3446_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3445_, 1, v___x_3450_);
                            v___x_3452_ = v___x_3445_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3454_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_currPos_3442_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3450_);
                            v___x_3452_ = v_reuseFailAlloc_3454_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_3455_ = lean_string_utf8_next_fast(v_fst_3402_, v_searcher_3443_);
                        v___x_3456_ = lean_nat_sub(v___x_3455_, v_searcher_3443_);
                        v___x_3457_ = lean_nat_add(v_searcher_3443_, v___x_3456_);
                        crate::leanh::lean_dec(v___x_3456_);
                        v_slice_3458_ = l_String_Slice_subslice_x21(
                            v___x_3405_,
                            v_currPos_3442_,
                            v_searcher_3443_,
                        );
                        crate::leanh::lean_inc(v___x_3457_);
                        if v_isShared_3446_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3445_, 1, v___x_3457_);
                            crate::leanh::lean_ctor_set(v___x_3445_, 0, v___x_3457_);
                            v_nextIt_3460_ = v___x_3445_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3463_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3457_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 1, v___x_3457_);
                            v_nextIt_3460_ = v_reuseFailAlloc_3463_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3445_);
                    crate::leanh::lean_dec(v_searcher_3443_);
                    v___x_3464_ = crate::leanh::lean_box(1);
                    v_it_3428_ = v___x_3464_;
                    v_startInclusive_3429_ = v_currPos_3442_;
                    v_endExclusive_3430_ = v___x_3403_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_3453_ = crate::leanh::lean_apply_4(
                    v_recur_3409_,
                    v___x_3452_,
                    v_acc_3407_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3453_;
            }
            7 => {
                v_startInclusive_3461_ = crate::leanh::lean_ctor_get(v_slice_3458_, 0);
                crate::leanh::lean_inc(v_startInclusive_3461_);
                v_endExclusive_3462_ = crate::leanh::lean_ctor_get(v_slice_3458_, 1);
                crate::leanh::lean_inc(v_endExclusive_3462_);
                crate::leanh::lean_dec_ref(v_slice_3458_);
                v_it_3428_ = v_nextIt_3460_;
                v_startInclusive_3429_ = v_startInclusive_3461_;
                v_endExclusive_3430_ = v_endExclusive_3462_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_instToString___lam__0___boxed(
    mut v___x_3466_: *mut crate::leanh::LeanObject,
    mut v___x_3467_: *mut crate::leanh::LeanObject,
    mut v___x_3468_: *mut crate::leanh::LeanObject,
    mut v_fst_3469_: *mut crate::leanh::LeanObject,
    mut v___x_3470_: *mut crate::leanh::LeanObject,
    mut v___x_3471_: *mut crate::leanh::LeanObject,
    mut v___x_3472_: *mut crate::leanh::LeanObject,
    mut v_it_3473_: *mut crate::leanh::LeanObject,
    mut v_acc_3474_: *mut crate::leanh::LeanObject,
    mut v_hP_3475_: *mut crate::leanh::LeanObject,
    mut v_recur_3476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1744__boxed_3477_: u32 = 0;
    let mut v_res_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1744__boxed_3477_ = crate::leanh::lean_unbox_uint32(v___x_3471_);
    crate::leanh::lean_dec(v___x_3471_);
    v_res_3478_ = l_Std_Http_Headers_instToString___lam__0(
        v___x_3466_,
        v___x_3467_,
        v___x_3468_,
        v_fst_3469_,
        v___x_3470_,
        v___x_1744__boxed_3477_,
        v___x_3472_,
        v_it_3473_,
        v_acc_3474_,
        v_hP_3475_,
        v_recur_3476_,
    );
    crate::leanh::lean_dec_ref(v___x_3472_);
    crate::leanh::lean_dec_ref(v_fst_3469_);
    crate::leanh::lean_dec(v___x_3468_);
    crate::leanh::lean_dec(v___x_3467_);
    crate::leanh::lean_dec_ref(v___x_3466_);
    return v_res_3478_;
}
pub unsafe fn _init_l_Std_Http_Headers_instToString___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3482_ = l_Std_Http_Headers_instToString___lam__1___closed__2;
    v___x_3483_ = lean_string_utf8_byte_size(v___x_3482_);
    return v___x_3483_;
}
pub unsafe fn _init_l_Std_Http_Headers_instToString___lam__1___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3484_: u32 = 0;
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3484_ = 45;
    v___x_3485_ = crate::leanh::lean_box_uint32(v___x_3484_);
    return v___x_3485_;
}
pub unsafe fn l_Std_Http_Headers_instToString___lam__1(
    mut v_x_3486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3487_ = crate::leanh::lean_ctor_get(v_x_3486_, 0);
                crate::leanh::lean_inc_n(v_fst_3487_, 2);
                v_snd_3488_ = crate::leanh::lean_ctor_get(v_x_3486_, 1);
                crate::leanh::lean_inc(v_snd_3488_);
                crate::leanh::lean_dec_ref(v_x_3486_);
                v___f_3494_ = l_Std_Http_Headers_instToString___lam__1___closed__1;
                v___x_3495_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3496_ = lean_string_utf8_byte_size(v_fst_3487_);
                v___x_3497_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3497_, 0, v_fst_3487_);
                crate::leanh::lean_ctor_set(v___x_3497_, 1, v___x_3495_);
                crate::leanh::lean_ctor_set(v___x_3497_, 2, v___x_3496_);
                crate::leanh::lean_inc_ref(v___x_3497_);
                v_it_3498_ = l_String_Slice_splitToSubslice___redArg(v___x_3497_, v___f_3494_);
                v___x_3499_ = l_Std_Http_Headers_instToString___lam__1___closed__2;
                v___x_3500_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Headers_instToString___lam__1___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Headers_instToString___lam__1___closed__3_once
                    ),
                    _init_l_Std_Http_Headers_instToString___lam__1___closed__3,
                );
                v___x_3501_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
                v___f_3502_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Headers_instToString___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_3502_, 0, v___x_3499_);
                crate::leanh::lean_closure_set(v___f_3502_, 1, v___x_3495_);
                crate::leanh::lean_closure_set(v___f_3502_, 2, v___x_3500_);
                crate::leanh::lean_closure_set(v___f_3502_, 3, v_fst_3487_);
                crate::leanh::lean_closure_set(v___f_3502_, 4, v___x_3496_);
                crate::leanh::lean_closure_set(v___f_3502_, 5, v___x_3501_);
                crate::leanh::lean_closure_set(v___f_3502_, 6, v___x_3497_);
                v___x_3503_ = crate::leanh::lean_box(0);
                v___x_3504_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_3502_,
                    v_it_3498_,
                    v___x_3503_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3504_) == 0 {
                    v___x_3505_ = l_Std_Http_Headers_get_x21___closed__0;
                    v___y_3490_ = v___x_3505_;
                    state = 1;
                    continue;
                } else {
                    v_val_3506_ = crate::leanh::lean_ctor_get(v___x_3504_, 0);
                    crate::leanh::lean_inc(v_val_3506_);
                    crate::leanh::lean_dec_ref_known(v___x_3504_, 1);
                    v___y_3490_ = v_val_3506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3491_ = l_Std_Http_Headers_instToString___lam__1___closed__0;
                v___x_3492_ = lean_string_append(v___y_3490_, v___x_3491_);
                v___x_3493_ = lean_string_append(v___x_3492_, v_snd_3488_);
                crate::leanh::lean_dec(v_snd_3488_);
                return v___x_3493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_instToString___lam__2(
    mut v___f_3508_: *mut crate::leanh::LeanObject,
    mut v_headers_3509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3512_: usize = 0;
    let mut v___x_3513_: usize = 0;
    let mut v_pairs_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_entries_3510_ = crate::leanh::lean_ctor_get(v_headers_3509_, 0);
    crate::leanh::lean_inc_ref(v_entries_3510_);
    crate::leanh::lean_dec_ref(v_headers_3509_);
    v___x_3511_ = l_Std_Http_Headers_getAll___redArg___closed__9;
    v_sz_3512_ = lean_array_size(v_entries_3510_);
    v___x_3513_ = 0usize;
    v_pairs_3514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3511_,
        v___f_3508_,
        v_sz_3512_,
        v___x_3513_,
        v_entries_3510_,
    );
    v___x_3515_ = l_Std_Http_Headers_instToString___lam__2___closed__0;
    v___x_3516_ = lean_array_to_list(v_pairs_3514_);
    v___x_3517_ = l_String_intercalate(v___x_3515_, v___x_3516_);
    return v___x_3517_;
}
pub unsafe fn l_Std_Http_Headers_instEncodeV11___lam__0(
    mut v___x_3522_: *mut crate::leanh::LeanObject,
    mut v___x_3523_: *mut crate::leanh::LeanObject,
    mut v___x_3524_: *mut crate::leanh::LeanObject,
    mut v_name_3525_: *mut crate::leanh::LeanObject,
    mut v___x_3526_: *mut crate::leanh::LeanObject,
    mut v___x_3527_: u32,
    mut v___x_3528_: *mut crate::leanh::LeanObject,
    mut v_it_3529_: *mut crate::leanh::LeanObject,
    mut v_acc_3530_: *mut crate::leanh::LeanObject,
    mut v_hP_3531_: *mut crate::leanh::LeanObject,
    mut v_recur_3532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_it_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: u32 = 0;
    let mut v___x_3556_: u32 = 0;
    let mut v___x_3557_: u8 = 0;
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: u32 = 0;
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u32 = 0;
    let mut v___x_3563_: u32 = 0;
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: u32 = 0;
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_it_3529_) == 0 {
                    v_currPos_3565_ = crate::leanh::lean_ctor_get(v_it_3529_, 0);
                    v_searcher_3566_ = crate::leanh::lean_ctor_get(v_it_3529_, 1);
                    v_isSharedCheck_3588_ = (!crate::leanh::lean_is_exclusive(v_it_3529_)) as u8;
                    if v_isSharedCheck_3588_ == 0 {
                        v___x_3568_ = v_it_3529_;
                        v_isShared_3569_ = v_isSharedCheck_3588_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_3566_);
                        crate::leanh::lean_inc(v_currPos_3565_);
                        crate::leanh::lean_dec(v_it_3529_);
                        v___x_3568_ = crate::leanh::lean_box(0);
                        v_isShared_3569_ = v_isSharedCheck_3588_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_recur_3532_);
                    crate::leanh::lean_dec(v___x_3526_);
                    return v_acc_3530_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_acc_3530_) == 0 {
                    v___x_3536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3536_, 0, v_out_3535_);
                    v___x_3537_ = crate::leanh::lean_apply_4(
                        v_recur_3532_,
                        v_it_3534_,
                        v___x_3536_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3537_;
                } else {
                    v_val_3538_ = crate::leanh::lean_ctor_get(v_acc_3530_, 0);
                    v_isSharedCheck_3549_ = (!crate::leanh::lean_is_exclusive(v_acc_3530_)) as u8;
                    if v_isSharedCheck_3549_ == 0 {
                        v___x_3540_ = v_acc_3530_;
                        v_isShared_3541_ = v_isSharedCheck_3549_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3538_);
                        crate::leanh::lean_dec(v_acc_3530_);
                        v___x_3540_ = crate::leanh::lean_box(0);
                        v_isShared_3541_ = v_isSharedCheck_3549_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3542_ = lean_string_utf8_extract(v___x_3522_, v___x_3523_, v___x_3524_);
                v___x_3543_ = lean_string_append(v_val_3538_, v___x_3542_);
                crate::leanh::lean_dec_ref(v___x_3542_);
                v___x_3544_ = lean_string_append(v___x_3543_, v_out_3535_);
                crate::leanh::lean_dec_ref(v_out_3535_);
                if v_isShared_3541_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3540_, 0, v___x_3544_);
                    v___x_3546_ = v___x_3540_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3548_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3544_);
                    v___x_3546_ = v_reuseFailAlloc_3548_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3547_ = crate::leanh::lean_apply_4(
                    v_recur_3532_,
                    v_it_3534_,
                    v___x_3546_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3547_;
            }
            4 => {
                v___x_3554_ = lean_string_utf8_extract(
                    v_name_3525_,
                    v_startInclusive_3552_,
                    v_endExclusive_3553_,
                );
                crate::leanh::lean_dec(v_endExclusive_3553_);
                crate::leanh::lean_dec(v_startInclusive_3552_);
                v___x_3555_ = lean_string_utf8_get(v___x_3554_, v___x_3523_);
                v___x_3556_ = 97;
                v___x_3557_ = lean_uint32_dec_le(v___x_3556_, v___x_3555_);
                if v___x_3557_ == 0 {
                    v___x_3558_ = lean_string_utf8_set(v___x_3554_, v___x_3523_, v___x_3555_);
                    v_it_3534_ = v_it_3551_;
                    v_out_3535_ = v___x_3558_;
                    state = 1;
                    continue;
                } else {
                    v___x_3559_ = 122;
                    v___x_3560_ = lean_uint32_dec_le(v___x_3555_, v___x_3559_);
                    if v___x_3560_ == 0 {
                        v___x_3561_ = lean_string_utf8_set(v___x_3554_, v___x_3523_, v___x_3555_);
                        v_it_3534_ = v_it_3551_;
                        v_out_3535_ = v___x_3561_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3562_ = 4294967264;
                        v___x_3563_ = lean_uint32_add(v___x_3555_, v___x_3562_);
                        v___x_3564_ = lean_string_utf8_set(v___x_3554_, v___x_3523_, v___x_3563_);
                        v_it_3534_ = v_it_3551_;
                        v_out_3535_ = v___x_3564_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3570_ = lean_nat_dec_eq(v_searcher_3566_, v___x_3526_);
                if v___x_3570_ == 0 {
                    crate::leanh::lean_dec(v___x_3526_);
                    v___x_3571_ = lean_string_utf8_get_fast(v_name_3525_, v_searcher_3566_);
                    v___x_3572_ = lean_uint32_dec_eq(v___x_3571_, v___x_3527_);
                    if v___x_3572_ == 0 {
                        v___x_3573_ = lean_string_utf8_next_fast(v_name_3525_, v_searcher_3566_);
                        crate::leanh::lean_dec(v_searcher_3566_);
                        if v_isShared_3569_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3568_, 1, v___x_3573_);
                            v___x_3575_ = v___x_3568_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3577_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_currPos_3565_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___x_3573_);
                            v___x_3575_ = v_reuseFailAlloc_3577_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_3578_ = lean_string_utf8_next_fast(v_name_3525_, v_searcher_3566_);
                        v___x_3579_ = lean_nat_sub(v___x_3578_, v_searcher_3566_);
                        v___x_3580_ = lean_nat_add(v_searcher_3566_, v___x_3579_);
                        crate::leanh::lean_dec(v___x_3579_);
                        v_slice_3581_ = l_String_Slice_subslice_x21(
                            v___x_3528_,
                            v_currPos_3565_,
                            v_searcher_3566_,
                        );
                        crate::leanh::lean_inc(v___x_3580_);
                        if v_isShared_3569_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3568_, 1, v___x_3580_);
                            crate::leanh::lean_ctor_set(v___x_3568_, 0, v___x_3580_);
                            v_nextIt_3583_ = v___x_3568_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3586_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3580_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 1, v___x_3580_);
                            v_nextIt_3583_ = v_reuseFailAlloc_3586_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3568_);
                    crate::leanh::lean_dec(v_searcher_3566_);
                    v___x_3587_ = crate::leanh::lean_box(1);
                    v_it_3551_ = v___x_3587_;
                    v_startInclusive_3552_ = v_currPos_3565_;
                    v_endExclusive_3553_ = v___x_3526_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_3576_ = crate::leanh::lean_apply_4(
                    v_recur_3532_,
                    v___x_3575_,
                    v_acc_3530_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3576_;
            }
            7 => {
                v_startInclusive_3584_ = crate::leanh::lean_ctor_get(v_slice_3581_, 0);
                crate::leanh::lean_inc(v_startInclusive_3584_);
                v_endExclusive_3585_ = crate::leanh::lean_ctor_get(v_slice_3581_, 1);
                crate::leanh::lean_inc(v_endExclusive_3585_);
                crate::leanh::lean_dec_ref(v_slice_3581_);
                v_it_3551_ = v_nextIt_3583_;
                v_startInclusive_3552_ = v_startInclusive_3584_;
                v_endExclusive_3553_ = v_endExclusive_3585_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_instEncodeV11___lam__0___boxed(
    mut v___x_3589_: *mut crate::leanh::LeanObject,
    mut v___x_3590_: *mut crate::leanh::LeanObject,
    mut v___x_3591_: *mut crate::leanh::LeanObject,
    mut v_name_3592_: *mut crate::leanh::LeanObject,
    mut v___x_3593_: *mut crate::leanh::LeanObject,
    mut v___x_3594_: *mut crate::leanh::LeanObject,
    mut v___x_3595_: *mut crate::leanh::LeanObject,
    mut v_it_3596_: *mut crate::leanh::LeanObject,
    mut v_acc_3597_: *mut crate::leanh::LeanObject,
    mut v_hP_3598_: *mut crate::leanh::LeanObject,
    mut v_recur_3599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_916__boxed_3600_: u32 = 0;
    let mut v_res_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_916__boxed_3600_ = crate::leanh::lean_unbox_uint32(v___x_3594_);
    crate::leanh::lean_dec(v___x_3594_);
    v_res_3601_ = l_Std_Http_Headers_instEncodeV11___lam__0(
        v___x_3589_,
        v___x_3590_,
        v___x_3591_,
        v_name_3592_,
        v___x_3593_,
        v___x_916__boxed_3600_,
        v___x_3595_,
        v_it_3596_,
        v_acc_3597_,
        v_hP_3598_,
        v_recur_3599_,
    );
    crate::leanh::lean_dec_ref(v___x_3595_);
    crate::leanh::lean_dec_ref(v_name_3592_);
    crate::leanh::lean_dec(v___x_3591_);
    crate::leanh::lean_dec(v___x_3590_);
    crate::leanh::lean_dec_ref(v___x_3589_);
    return v_res_3601_;
}
pub unsafe fn l_Std_Http_Headers_instEncodeV11___lam__1(
    mut v_buf_3602_: *mut crate::leanh::LeanObject,
    mut v_name_3603_: *mut crate::leanh::LeanObject,
    mut v_value_3604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3611_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut v___f_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3625_ = l_Std_Http_Headers_instToString___lam__1___closed__1;
                v___x_3626_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3627_ = lean_string_utf8_byte_size(v_name_3603_);
                crate::leanh::lean_inc_ref(v_name_3603_);
                v___x_3628_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3628_, 0, v_name_3603_);
                crate::leanh::lean_ctor_set(v___x_3628_, 1, v___x_3626_);
                crate::leanh::lean_ctor_set(v___x_3628_, 2, v___x_3627_);
                crate::leanh::lean_inc_ref(v___x_3628_);
                v_it_3629_ = l_String_Slice_splitToSubslice___redArg(v___x_3628_, v___f_3625_);
                v___x_3630_ = l_Std_Http_Headers_instToString___lam__1___closed__2;
                v___x_3631_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Headers_instToString___lam__1___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Std_Http_Headers_instToString___lam__1___closed__3_once
                    ),
                    _init_l_Std_Http_Headers_instToString___lam__1___closed__3,
                );
                v___x_3632_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
                v___f_3633_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Headers_instEncodeV11___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_3633_, 0, v___x_3630_);
                crate::leanh::lean_closure_set(v___f_3633_, 1, v___x_3626_);
                crate::leanh::lean_closure_set(v___f_3633_, 2, v___x_3631_);
                crate::leanh::lean_closure_set(v___f_3633_, 3, v_name_3603_);
                crate::leanh::lean_closure_set(v___f_3633_, 4, v___x_3627_);
                crate::leanh::lean_closure_set(v___f_3633_, 5, v___x_3632_);
                crate::leanh::lean_closure_set(v___f_3633_, 6, v___x_3628_);
                v___x_3634_ = crate::leanh::lean_box(0);
                v___x_3635_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_3633_,
                    v_it_3629_,
                    v___x_3634_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3635_) == 0 {
                    v___x_3636_ = l_Std_Http_Headers_get_x21___closed__0;
                    v___y_3606_ = v___x_3636_;
                    state = 1;
                    continue;
                } else {
                    v_val_3637_ = crate::leanh::lean_ctor_get(v___x_3635_, 0);
                    crate::leanh::lean_inc(v_val_3637_);
                    crate::leanh::lean_dec_ref_known(v___x_3635_, 1);
                    v___y_3606_ = v_val_3637_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_data_3607_ = crate::leanh::lean_ctor_get(v_buf_3602_, 0);
                v_size_3608_ = crate::leanh::lean_ctor_get(v_buf_3602_, 1);
                v_isSharedCheck_3624_ = (!crate::leanh::lean_is_exclusive(v_buf_3602_)) as u8;
                if v_isSharedCheck_3624_ == 0 {
                    v___x_3610_ = v_buf_3602_;
                    v_isShared_3611_ = v_isSharedCheck_3624_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_3608_);
                    crate::leanh::lean_inc(v_data_3607_);
                    crate::leanh::lean_dec(v_buf_3602_);
                    v___x_3610_ = crate::leanh::lean_box(0);
                    v_isShared_3611_ = v_isSharedCheck_3624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3612_ = l_Std_Http_Headers_instToString___lam__1___closed__0;
                v___x_3613_ = lean_string_append(v___y_3606_, v___x_3612_);
                v___x_3614_ = lean_string_append(v___x_3613_, v_value_3604_);
                v___x_3615_ = l_Std_Http_Headers_instToString___lam__2___closed__0;
                v___x_3616_ = lean_string_append(v___x_3614_, v___x_3615_);
                v___x_3617_ = lean_string_to_utf8(v___x_3616_);
                crate::leanh::lean_dec_ref(v___x_3616_);
                crate::leanh::lean_inc_ref(v___x_3617_);
                v___x_3618_ = lean_array_push(v_data_3607_, v___x_3617_);
                v___x_3619_ = lean_byte_array_size(v___x_3617_);
                crate::leanh::lean_dec_ref(v___x_3617_);
                v___x_3620_ = lean_nat_add(v_size_3608_, v___x_3619_);
                crate::leanh::lean_dec(v_size_3608_);
                if v_isShared_3611_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3610_, 1, v___x_3620_);
                    crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3618_);
                    v___x_3622_ = v___x_3610_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 1, v___x_3620_);
                    v___x_3622_ = v_reuseFailAlloc_3623_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_instEncodeV11___lam__1___boxed(
    mut v_buf_3638_: *mut crate::leanh::LeanObject,
    mut v_name_3639_: *mut crate::leanh::LeanObject,
    mut v_value_3640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3641_ =
        l_Std_Http_Headers_instEncodeV11___lam__1(v_buf_3638_, v_name_3639_, v_value_3640_);
    crate::leanh::lean_dec_ref(v_value_3640_);
    return v_res_3641_;
}
pub unsafe fn l_Std_Http_Headers_instEncodeV11___lam__2(
    mut v___f_3642_: *mut crate::leanh::LeanObject,
    mut v_buffer_3643_: *mut crate::leanh::LeanObject,
    mut v_headers_3644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3645_ = l_Std_Http_Headers_fold___redArg(v_headers_3644_, v_buffer_3643_, v___f_3642_);
    return v___x_3645_;
}
pub unsafe fn l_Std_Http_Headers_instEncodeV11___lam__2___boxed(
    mut v___f_3646_: *mut crate::leanh::LeanObject,
    mut v_buffer_3647_: *mut crate::leanh::LeanObject,
    mut v_headers_3648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3649_ =
        l_Std_Http_Headers_instEncodeV11___lam__2(v___f_3646_, v_buffer_3647_, v_headers_3648_);
    crate::leanh::lean_dec_ref(v_headers_3648_);
    return v_res_3649_;
}
pub unsafe fn _init_l_Std_Http_Headers_instEmptyCollection() -> *mut crate::leanh::LeanObject {
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3654_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0_once),
        _init_l_Std_Http_Headers_empty___closed__0,
    );
    return v___x_3654_;
}
pub unsafe fn l_Std_Http_Headers_instSingletonProdNameValue___lam__1(
    mut v_x_3655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3656_ = crate::leanh::lean_ctor_get(v_x_3655_, 0);
    crate::leanh::lean_inc(v_fst_3656_);
    v___x_3657_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Headers_empty___closed__0_once),
        _init_l_Std_Http_Headers_empty___closed__0,
    );
    v_entries_3658_ = crate::leanh::lean_ctor_get(v___x_3657_, 0);
    v_indexes_3659_ = crate::leanh::lean_ctor_get(v___x_3657_, 1);
    v___f_3660_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
    v___f_3661_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
    v_i_3662_ = lean_array_get_size(v_entries_3658_);
    v_f_3663_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Headers_insert___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v_f_3663_, 0, v_i_3662_);
    crate::leanh::lean_inc_ref(v_entries_3658_);
    v_entries_3664_ = lean_array_push(v_entries_3658_, v_x_3655_);
    crate::leanh::lean_inc_ref(v_indexes_3659_);
    v_indexes_3665_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
        v___f_3660_,
        v___f_3661_,
        v_indexes_3659_,
        v_fst_3656_,
        v_f_3663_,
    );
    v___x_3666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3666_, 0, v_entries_3664_);
    crate::leanh::lean_ctor_set(v___x_3666_, 1, v_indexes_3665_);
    return v___x_3666_;
}
pub unsafe fn l_Std_Http_Headers_instInsertProdNameValue___lam__1(
    mut v_x_3669_: *mut crate::leanh::LeanObject,
    mut v_s_3670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___f_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexes_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3671_ = crate::leanh::lean_ctor_get(v_x_3669_, 0);
                crate::leanh::lean_inc(v_fst_3671_);
                v_entries_3672_ = crate::leanh::lean_ctor_get(v_s_3670_, 0);
                v_indexes_3673_ = crate::leanh::lean_ctor_get(v_s_3670_, 1);
                v_isSharedCheck_3686_ = (!crate::leanh::lean_is_exclusive(v_s_3670_)) as u8;
                if v_isSharedCheck_3686_ == 0 {
                    v___x_3675_ = v_s_3670_;
                    v_isShared_3676_ = v_isSharedCheck_3686_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_indexes_3673_);
                    crate::leanh::lean_inc(v_entries_3672_);
                    crate::leanh::lean_dec(v_s_3670_);
                    v___x_3675_ = crate::leanh::lean_box(0);
                    v_isShared_3676_ = v_isSharedCheck_3686_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3677_ = l_Std_Http_instDecidableMemNameHeaders___closed__0;
                v___f_3678_ = l_Std_Http_instDecidableMemNameHeaders___closed__1;
                v_i_3679_ = lean_array_get_size(v_entries_3672_);
                v_f_3680_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Headers_insert___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v_f_3680_, 0, v_i_3679_);
                v_entries_3681_ = lean_array_push(v_entries_3672_, v_x_3669_);
                v_indexes_3682_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(
                    v___f_3677_,
                    v___f_3678_,
                    v_indexes_3673_,
                    v_fst_3671_,
                    v_f_3680_,
                );
                if v_isShared_3676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3675_, 1, v_indexes_3682_);
                    crate::leanh::lean_ctor_set(v___x_3675_, 0, v_entries_3681_);
                    v___x_3684_ = v___x_3675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_entries_3681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_indexes_3682_);
                    v___x_3684_ = v_reuseFailAlloc_3685_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(
    mut v_f_3691_: *mut crate::leanh::LeanObject,
    mut v_a_3692_: *mut crate::leanh::LeanObject,
    mut v_x_3693_: *mut crate::leanh::LeanObject,
    mut v___y_3694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3695_ = crate::leanh::lean_apply_2(v_f_3691_, v_a_3692_, v___y_3694_);
    return v___x_3695_;
}
pub unsafe fn l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(
    mut v_inst_3696_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3697_: *mut crate::leanh::LeanObject,
    mut v_headers_3698_: *mut crate::leanh::LeanObject,
    mut v_b_3699_: *mut crate::leanh::LeanObject,
    mut v_f_3700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_entries_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3703_: usize = 0;
    let mut v___x_3704_: usize = 0;
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_entries_3701_ = crate::leanh::lean_ctor_get(v_headers_3698_, 0);
    crate::leanh::lean_inc_ref(v_entries_3701_);
    crate::leanh::lean_dec_ref(v_headers_3698_);
    v___f_3702_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3702_, 0, v_f_3700_);
    v_sz_3703_ = lean_array_size(v_entries_3701_);
    v___x_3704_ = 0usize;
    v___x_3705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_3696_,
        v_entries_3701_,
        v___f_3702_,
        v_sz_3703_,
        v___x_3704_,
        v_b_3699_,
    );
    return v___x_3705_;
}
pub unsafe fn l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(
    mut v_inst_3706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3707_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3707_, 0, v_inst_3706_);
    return v___f_3707_;
}
pub unsafe fn l_Std_Http_Headers_instForInProdNameValueOfMonad(
    mut v_m_3708_: *mut crate::leanh::LeanObject,
    mut v_inst_3709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3710_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3710_, 0, v_inst_3709_);
    return v___f_3710_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Headers(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Data_Headers_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Http_instInhabitedHeaders_default = _init_l_Std_Http_instInhabitedHeaders_default();
    crate::leanh::lean_mark_persistent(l_Std_Http_instInhabitedHeaders_default);
    l_Std_Http_instInhabitedHeaders = _init_l_Std_Http_instInhabitedHeaders();
    crate::leanh::lean_mark_persistent(l_Std_Http_instInhabitedHeaders);
    l_Std_Http_instMembershipNameHeaders = _init_l_Std_Http_instMembershipNameHeaders();
    crate::leanh::lean_mark_persistent(l_Std_Http_instMembershipNameHeaders);
    l_Std_Http_Headers_empty = _init_l_Std_Http_Headers_empty();
    crate::leanh::lean_mark_persistent(l_Std_Http_Headers_empty);
    l_Std_Http_Headers_instToString___lam__1___boxed__const__1 =
        _init_l_Std_Http_Headers_instToString___lam__1___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_Std_Http_Headers_instToString___lam__1___boxed__const__1);
    l_Std_Http_Headers_instEmptyCollection = _init_l_Std_Http_Headers_instEmptyCollection();
    crate::leanh::lean_mark_persistent(l_Std_Http_Headers_instEmptyCollection);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Headers(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Headers(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Data_Headers_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Headers_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Headers_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Headers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Headers(builtin);
}
