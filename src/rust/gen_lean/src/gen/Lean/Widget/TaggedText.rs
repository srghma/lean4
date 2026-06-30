// Lean compiler output
// Module: Lean.Widget.TaggedText
// Imports: Lean.Server.Rpc.Basic Init.Data.Array.GetLit Init.Data.String.Length
use crate::ffi::{
    lean_array_get, lean_array_get_borrowed, lean_array_get_size, lean_array_pop, lean_array_push,
    lean_array_set, lean_array_size, lean_array_uget, lean_array_uset, lean_int_add,
    lean_int_dec_lt, lean_int_sub, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int,
    lean_panic_fn_borrowed, lean_string_append, lean_string_dec_eq, lean_string_length,
    lean_string_posof, lean_string_push, lean_string_pushn, lean_string_utf8_byte_size,
    lean_string_utf8_extract, lean_string_utf8_next, lean_usize_add, lean_usize_dec_lt,
    lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Except::{
    l_ExceptT_bind, l_ExceptT_instMonad___redArg___lam__1, l_ExceptT_instMonad___redArg___lam__4,
    l_ExceptT_instMonad___redArg___lam__7, l_ExceptT_instMonad___redArg___lam__9, l_ExceptT_map,
    l_ExceptT_pure,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_get, l_StateT_instMonad___redArg___lam__1,
    l_StateT_instMonad___redArg___lam__4, l_StateT_instMonad___redArg___lam__7,
    l_StateT_instMonad___redArg___lam__9, l_StateT_map, l_StateT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
    l_Array_isEqvAux___redArg, l_Array_repr___redArg, l_Array_reverse___redArg,
};
use crate::r#gen::Init::Data::Array::GetLit::{
    initialize_Init_Data_Array_GetLit, runtime_initialize_Init_Data_Array_GetLit,
};
use crate::r#gen::Init::Data::Format::Basic::{
    l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27,
    l_Std_Format_FlattenAllowability_shouldFlatten, l_Std_Format_instBEqFlattenAllowability_beq,
    l_Std_Format_instBEqFlattenBehavior_beq,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::List::Basic::l_List_drop___redArg;
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Data::Nat::Basic::l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop;
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Prelude::{
    l_List_foldl___redArg, l_ReaderT_instMonad___redArg, l_id___boxed,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Lean::Data::Json::Basic::{l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Array_fromJson_x3f___redArg, l_Array_toJson___redArg, l_Lean_Json_getTag_x3f,
    l_Lean_Json_parseCtorFields, l_Lean_instFromJsonJson___lam__0,
};
use crate::r#gen::Lean::Server::Rpc::Basic::{
    initialize_Lean_Server_Rpc_Basic, runtime_initialize_Lean_Server_Rpc_Basic,
};
pub static l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value:
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
static mut l_Lean_Widget_instInhabitedTaggedText_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instInhabitedTaggedText_default___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instInhabitedTaggedText_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instInhabitedTaggedText_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Widget_instInhabitedTaggedText___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Widget_instInhabitedTaggedText___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        76, 101, 97, 110, 46, 87, 105, 100, 103, 101, 116, 46, 84, 97, 103, 103, 101, 100, 84, 101,
        120, 116, 46, 116, 101, 120, 116, 0,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        76, 101, 97, 110, 46, 87, 105, 100, 103, 101, 116, 46, 84, 97, 103, 103, 101, 100, 84, 101,
        120, 116, 46, 97, 112, 112, 101, 110, 100, 0,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        76, 101, 97, 110, 46, 87, 105, 100, 103, 101, 116, 46, 84, 97, 103, 103, 101, 100, 84, 101,
        120, 116, 46, 116, 97, 103, 0,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111,
        117, 110, 100, 0,
    ],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [97, 112, 112, 101, 110, 100, 0],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 120, 116, 0],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [116, 97, 103, 0],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_map as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_pure as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_bind as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instFromJsonJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_TaggedText_instInhabitedTaggedState_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6_value: leanh::LeanClosureObject<3> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_get as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7_value: leanh::LeanClosureObject<7> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*7) as u16, other: 0, tag: 245 }, m_fun: l_StateT_bind as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 7, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8_value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8_value) as *mut leanh::LeanObject;
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0]};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Widget_TaggedText_ctorIdx___redArg(
    mut v_x_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1562_) {
        0 => {
            let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1563_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1563_;
        }
        1 => {
            let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1564_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1564_;
        }
        _ => {
            let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1565_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1565_;
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorIdx___redArg___boxed(
    mut v_x_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1567_ = l_Lean_Widget_TaggedText_ctorIdx___redArg(v_x_1566_);
    leanh::lean_dec_ref(v_x_1566_);
    return v_res_1567_;
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorIdx(
    mut v_00_u03b1_1568_: *mut leanh::LeanObject,
    mut v_x_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1570_ = l_Lean_Widget_TaggedText_ctorIdx___redArg(v_x_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorIdx___boxed(
    mut v_00_u03b1_1571_: *mut leanh::LeanObject,
    mut v_x_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1573_ = l_Lean_Widget_TaggedText_ctorIdx(v_00_u03b1_1571_, v_x_1572_);
    leanh::lean_dec_ref(v_x_1572_);
    return v_res_1573_;
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorElim___redArg(
    mut v_t_1574_: *mut leanh::LeanObject,
    mut v_k_1575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1574_) == 2 {
        let mut v_a_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1576_ = leanh::lean_ctor_get(v_t_1574_, 0);
        leanh::lean_inc(v_a_1576_);
        v_a_1577_ = leanh::lean_ctor_get(v_t_1574_, 1);
        leanh::lean_inc_ref(v_a_1577_);
        leanh::lean_dec_ref_known(v_t_1574_, 2);
        v___x_1578_ = leanh::lean_apply_2(v_k_1575_, v_a_1576_, v_a_1577_);
        return v___x_1578_;
    } else {
        let mut v_a_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1579_ = leanh::lean_ctor_get(v_t_1574_, 0);
        leanh::lean_inc_ref(v_a_1579_);
        leanh::lean_dec_ref(v_t_1574_);
        v___x_1580_ = leanh::lean_apply_1(v_k_1575_, v_a_1579_);
        return v___x_1580_;
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorElim(
    mut v_00_u03b1_1581_: *mut leanh::LeanObject,
    mut v_motive__1_1582_: *mut leanh::LeanObject,
    mut v_ctorIdx_1583_: *mut leanh::LeanObject,
    mut v_t_1584_: *mut leanh::LeanObject,
    mut v_h_1585_: *mut leanh::LeanObject,
    mut v_k_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1584_, v_k_1586_);
    return v___x_1587_;
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorElim___boxed(
    mut v_00_u03b1_1588_: *mut leanh::LeanObject,
    mut v_motive__1_1589_: *mut leanh::LeanObject,
    mut v_ctorIdx_1590_: *mut leanh::LeanObject,
    mut v_t_1591_: *mut leanh::LeanObject,
    mut v_h_1592_: *mut leanh::LeanObject,
    mut v_k_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Lean_Widget_TaggedText_ctorElim(
        v_00_u03b1_1588_,
        v_motive__1_1589_,
        v_ctorIdx_1590_,
        v_t_1591_,
        v_h_1592_,
        v_k_1593_,
    );
    leanh::lean_dec(v_ctorIdx_1590_);
    return v_res_1594_;
}
pub unsafe fn l_Lean_Widget_TaggedText_text_elim___redArg(
    mut v_t_1595_: *mut leanh::LeanObject,
    mut v_text_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1595_, v_text_1596_);
    return v___x_1597_;
}
pub unsafe fn l_Lean_Widget_TaggedText_text_elim(
    mut v_00_u03b1_1598_: *mut leanh::LeanObject,
    mut v_motive__1_1599_: *mut leanh::LeanObject,
    mut v_t_1600_: *mut leanh::LeanObject,
    mut v_h_1601_: *mut leanh::LeanObject,
    mut v_text_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1600_, v_text_1602_);
    return v___x_1603_;
}
pub unsafe fn l_Lean_Widget_TaggedText_append_elim___redArg(
    mut v_t_1604_: *mut leanh::LeanObject,
    mut v_append_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1604_, v_append_1605_);
    return v___x_1606_;
}
pub unsafe fn l_Lean_Widget_TaggedText_append_elim(
    mut v_00_u03b1_1607_: *mut leanh::LeanObject,
    mut v_motive__1_1608_: *mut leanh::LeanObject,
    mut v_t_1609_: *mut leanh::LeanObject,
    mut v_h_1610_: *mut leanh::LeanObject,
    mut v_append_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1612_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1609_, v_append_1611_);
    return v___x_1612_;
}
pub unsafe fn l_Lean_Widget_TaggedText_tag_elim___redArg(
    mut v_t_1613_: *mut leanh::LeanObject,
    mut v_tag_1614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1615_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1613_, v_tag_1614_);
    return v___x_1615_;
}
pub unsafe fn l_Lean_Widget_TaggedText_tag_elim(
    mut v_00_u03b1_1616_: *mut leanh::LeanObject,
    mut v_motive__1_1617_: *mut leanh::LeanObject,
    mut v_t_1618_: *mut leanh::LeanObject,
    mut v_h_1619_: *mut leanh::LeanObject,
    mut v_tag_1620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1618_, v_tag_1620_);
    return v___x_1621_;
}
pub unsafe fn l_Lean_Widget_instInhabitedTaggedText_default(
    mut v_00_u03b1_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = l_Lean_Widget_instInhabitedTaggedText_default___closed__1;
    return v___x_1626_;
}
pub unsafe fn _init_l_Lean_Widget_instInhabitedTaggedText___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Lean_Widget_instInhabitedTaggedText_default(leanh::lean_box(0));
    return v___x_1627_;
}
pub unsafe fn l_Lean_Widget_instInhabitedTaggedText(
    mut v_a_1628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0_once),
        _init_l_Lean_Widget_instInhabitedTaggedText___closed__0,
    );
    return v___x_1629_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed(
    mut v_inst_1630_: *mut leanh::LeanObject,
    mut v_x_1631_: *mut leanh::LeanObject,
    mut v_x_1632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1633_: u8 = 0;
    let mut v_r_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1633_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_1630_, v_x_1631_, v_x_1632_);
    v_r_1634_ = leanh::lean_box((v_res_1633_) as usize);
    return v_r_1634_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText_beq___redArg(
    mut v_inst_1635_: *mut leanh::LeanObject,
    mut v_x_1636_: *mut leanh::LeanObject,
    mut v_x_1637_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_a_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: u8 = 0;
    let mut v_a_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: u8 = 0;
    let mut v_a_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1636_) {
                0 => {
                    leanh::lean_dec_ref(v_inst_1635_);
                    if leanh::lean_obj_tag(v_x_1637_) == 0 {
                        v_a_1638_ = leanh::lean_ctor_get(v_x_1636_, 0);
                        leanh::lean_inc_ref(v_a_1638_);
                        leanh::lean_dec_ref_known(v_x_1636_, 1);
                        v_a_1639_ = leanh::lean_ctor_get(v_x_1637_, 0);
                        leanh::lean_inc_ref(v_a_1639_);
                        leanh::lean_dec_ref_known(v_x_1637_, 1);
                        v___x_1640_ = lean_string_dec_eq(v_a_1638_, v_a_1639_);
                        leanh::lean_dec_ref(v_a_1639_);
                        leanh::lean_dec_ref(v_a_1638_);
                        return v___x_1640_;
                    } else {
                        leanh::lean_dec_ref_known(v_x_1636_, 1);
                        leanh::lean_dec_ref(v_x_1637_);
                        v___x_1641_ = 0;
                        return v___x_1641_;
                    }
                }
                1 => {
                    if leanh::lean_obj_tag(v_x_1637_) == 1 {
                        v_a_1642_ = leanh::lean_ctor_get(v_x_1636_, 0);
                        leanh::lean_inc_ref(v_a_1642_);
                        leanh::lean_dec_ref_known(v_x_1636_, 1);
                        v_a_1643_ = leanh::lean_ctor_get(v_x_1637_, 0);
                        leanh::lean_inc_ref(v_a_1643_);
                        leanh::lean_dec_ref_known(v_x_1637_, 1);
                        v___x_1644_ = lean_array_get_size(v_a_1642_);
                        v___x_1645_ = lean_array_get_size(v_a_1643_);
                        v___x_1646_ = lean_nat_dec_eq(v___x_1644_, v___x_1645_);
                        if v___x_1646_ == 0 {
                            leanh::lean_dec_ref(v_a_1643_);
                            leanh::lean_dec_ref(v_a_1642_);
                            leanh::lean_dec_ref(v_inst_1635_);
                            return v___x_1646_;
                        } else {
                            v___x_1647_ = leanh::lean_alloc_closure(
                                l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                1,
                            );
                            leanh::lean_closure_set(v___x_1647_, 0, v_inst_1635_);
                            v___x_1648_ = l_Array_isEqvAux___redArg(
                                v_a_1642_,
                                v_a_1643_,
                                v___x_1647_,
                                v___x_1644_,
                            );
                            leanh::lean_dec_ref(v_a_1643_);
                            leanh::lean_dec_ref(v_a_1642_);
                            return v___x_1648_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_1636_, 1);
                        leanh::lean_dec_ref(v_x_1637_);
                        leanh::lean_dec_ref(v_inst_1635_);
                        v___x_1649_ = 0;
                        return v___x_1649_;
                    }
                }
                _ => {
                    if leanh::lean_obj_tag(v_x_1637_) == 2 {
                        v_a_1650_ = leanh::lean_ctor_get(v_x_1636_, 0);
                        leanh::lean_inc(v_a_1650_);
                        v_a_1651_ = leanh::lean_ctor_get(v_x_1636_, 1);
                        leanh::lean_inc_ref(v_a_1651_);
                        leanh::lean_dec_ref_known(v_x_1636_, 2);
                        v_a_1652_ = leanh::lean_ctor_get(v_x_1637_, 0);
                        leanh::lean_inc(v_a_1652_);
                        v_a_1653_ = leanh::lean_ctor_get(v_x_1637_, 1);
                        leanh::lean_inc_ref(v_a_1653_);
                        leanh::lean_dec_ref_known(v_x_1637_, 2);
                        leanh::lean_inc_ref(v_inst_1635_);
                        v___x_1654_ =
                            leanh::lean_apply_2(v_inst_1635_, v_a_1650_, v_a_1652_);
                        v___x_1655_ = (leanh::lean_unbox(v___x_1654_) as u8);
                        if v___x_1655_ == 0 {
                            leanh::lean_dec_ref(v_a_1653_);
                            leanh::lean_dec_ref(v_a_1651_);
                            leanh::lean_dec_ref(v_inst_1635_);
                            v___x_1656_ = (leanh::lean_unbox(v___x_1654_) as u8);
                            return v___x_1656_;
                        } else {
                            v_x_1636_ = v_a_1651_;
                            v_x_1637_ = v_a_1653_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_1636_, 2);
                        leanh::lean_dec_ref(v_x_1637_);
                        leanh::lean_dec_ref(v_inst_1635_);
                        v___x_1658_ = 0;
                        return v___x_1658_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText_beq(
    mut v_00_u03b1_1659_: *mut leanh::LeanObject,
    mut v_inst_1660_: *mut leanh::LeanObject,
    mut v_x_1661_: *mut leanh::LeanObject,
    mut v_x_1662_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1663_: u8 = 0;
    v___x_1663_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_1660_, v_x_1661_, v_x_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText_beq___boxed(
    mut v_00_u03b1_1664_: *mut leanh::LeanObject,
    mut v_inst_1665_: *mut leanh::LeanObject,
    mut v_x_1666_: *mut leanh::LeanObject,
    mut v_x_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1668_: u8 = 0;
    let mut v_r_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ =
        l_Lean_Widget_instBEqTaggedText_beq(v_00_u03b1_1664_, v_inst_1665_, v_x_1666_, v_x_1667_);
    v_r_1669_ = leanh::lean_box((v_res_1668_) as usize);
    return v_r_1669_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText___redArg(
    mut v_inst_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = leanh::lean_alloc_closure(
        l_Lean_Widget_instBEqTaggedText_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_1671_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1671_, 1, v_inst_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText(
    mut v_00_u03b1_1672_: *mut leanh::LeanObject,
    mut v_inst_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = leanh::lean_alloc_closure(
        l_Lean_Widget_instBEqTaggedText_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_1674_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1674_, 1, v_inst_1673_);
    return v___x_1674_;
}
pub unsafe fn _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = leanh::lean_unsigned_to_nat(2);
    v___x_1682_ = lean_nat_to_int(v___x_1681_);
    return v___x_1682_;
}
pub unsafe fn _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = leanh::lean_unsigned_to_nat(1);
    v___x_1684_ = lean_nat_to_int(v___x_1683_);
    return v___x_1684_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText_repr___redArg___boxed(
    mut v_inst_1697_: *mut leanh::LeanObject,
    mut v_x_1698_: *mut leanh::LeanObject,
    mut v_prec_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1700_ =
        l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_1697_, v_x_1698_, v_prec_1699_);
    leanh::lean_dec(v_prec_1699_);
    return v_res_1700_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText_repr___redArg(
    mut v_inst_1701_: *mut leanh::LeanObject,
    mut v_x_1702_: *mut leanh::LeanObject,
    mut v_prec_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1707_: u8 = 0;
    let mut v___y_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1724_: u8 = 0;
    let mut v_a_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localinst_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: u8 = 0;
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: u8 = 0;
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1702_) {
                0 => {
                    leanh::lean_dec_ref(v_inst_1701_);
                    v_a_1704_ = leanh::lean_ctor_get(v_x_1702_, 0);
                    v_isSharedCheck_1724_ = (!leanh::lean_is_exclusive(v_x_1702_)) as u8;
                    if v_isSharedCheck_1724_ == 0 {
                        v___x_1706_ = v_x_1702_;
                        v_isShared_1707_ = v_isSharedCheck_1724_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1704_);
                        leanh::lean_dec(v_x_1702_);
                        v___x_1706_ = leanh::lean_box(0);
                        v_isShared_1707_ = v_isSharedCheck_1724_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_1725_ = leanh::lean_ctor_get(v_x_1702_, 0);
                    leanh::lean_inc_ref(v_a_1725_);
                    leanh::lean_dec_ref_known(v_x_1702_, 1);
                    v_localinst_1726_ = leanh::lean_alloc_closure(
                        l_Lean_Widget_instReprTaggedText_repr___redArg___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    leanh::lean_closure_set(v_localinst_1726_, 0, v_inst_1701_);
                    v___x_1736_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1737_ = lean_nat_dec_le(v___x_1736_, v_prec_1703_);
                    if v___x_1737_ == 0 {
                        v___x_1738_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once
                            ),
                            _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3,
                        );
                        v___y_1728_ = v___x_1738_;
                        state = 4;
                        continue;
                    } else {
                        v___x_1739_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once
                            ),
                            _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4,
                        );
                        v___y_1728_ = v___x_1739_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v_a_1740_ = leanh::lean_ctor_get(v_x_1702_, 0);
                    v_a_1741_ = leanh::lean_ctor_get(v_x_1702_, 1);
                    v_isSharedCheck_1764_ = (!leanh::lean_is_exclusive(v_x_1702_)) as u8;
                    if v_isSharedCheck_1764_ == 0 {
                        v___x_1743_ = v_x_1702_;
                        v_isShared_1744_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1741_);
                        leanh::lean_inc(v_a_1740_);
                        leanh::lean_dec(v_x_1702_);
                        v___x_1743_ = leanh::lean_box(0);
                        v_isShared_1744_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1720_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1721_ = lean_nat_dec_le(v___x_1720_, v_prec_1703_);
                if v___x_1721_ == 0 {
                    v___x_1722_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once
                        ),
                        _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3,
                    );
                    v___y_1709_ = v___x_1722_;
                    state = 2;
                    continue;
                } else {
                    v___x_1723_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once
                        ),
                        _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4,
                    );
                    v___y_1709_ = v___x_1723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1710_ = l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2;
                v___x_1711_ = l_String_quote(v_a_1704_);
                if v_isShared_1707_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1706_, 3);
                    leanh::lean_ctor_set(v___x_1706_, 0, v___x_1711_);
                    v___x_1713_ = v___x_1706_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1719_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1711_);
                    v___x_1713_ = v_reuseFailAlloc_1719_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1714_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1714_, 0, v___x_1710_);
                leanh::lean_ctor_set(v___x_1714_, 1, v___x_1713_);
                leanh::lean_inc(v___y_1709_);
                v___x_1715_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1715_, 0, v___y_1709_);
                leanh::lean_ctor_set(v___x_1715_, 1, v___x_1714_);
                v___x_1716_ = 0;
                v___x_1717_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1717_, 0, v___x_1715_);
                leanh::lean_ctor_set_uint8(
                    v___x_1717_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1716_,
                );
                v___x_1718_ = l_Repr_addAppParen(v___x_1717_, v_prec_1703_);
                return v___x_1718_;
            }
            4 => {
                v___x_1729_ = l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7;
                v___x_1730_ = l_Array_repr___redArg(v_localinst_1726_, v_a_1725_);
                v___x_1731_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1731_, 0, v___x_1729_);
                leanh::lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                leanh::lean_inc(v___y_1728_);
                v___x_1732_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1732_, 0, v___y_1728_);
                leanh::lean_ctor_set(v___x_1732_, 1, v___x_1731_);
                v___x_1733_ = 0;
                v___x_1734_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1734_, 0, v___x_1732_);
                leanh::lean_ctor_set_uint8(
                    v___x_1734_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1733_,
                );
                v___x_1735_ = l_Repr_addAppParen(v___x_1734_, v_prec_1703_);
                return v___x_1735_;
            }
            5 => {
                v___x_1745_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1761_ = lean_nat_dec_le(v___x_1745_, v_prec_1703_);
                if v___x_1761_ == 0 {
                    v___x_1762_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once
                        ),
                        _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3,
                    );
                    v___y_1747_ = v___x_1762_;
                    state = 6;
                    continue;
                } else {
                    v___x_1763_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once
                        ),
                        _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4,
                    );
                    v___y_1747_ = v___x_1763_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1748_ = leanh::lean_box(1);
                v___x_1749_ = l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10;
                leanh::lean_inc_ref(v_inst_1701_);
                v___x_1750_ = leanh::lean_apply_2(v_inst_1701_, v_a_1740_, v___x_1745_);
                if v_isShared_1744_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1743_, 5);
                    leanh::lean_ctor_set(v___x_1743_, 1, v___x_1750_);
                    leanh::lean_ctor_set(v___x_1743_, 0, v___x_1749_);
                    v___x_1752_ = v___x_1743_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1750_);
                    v___x_1752_ = v_reuseFailAlloc_1760_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1753_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1753_, 0, v___x_1752_);
                leanh::lean_ctor_set(v___x_1753_, 1, v___x_1748_);
                v___x_1754_ = l_Lean_Widget_instReprTaggedText_repr___redArg(
                    v_inst_1701_,
                    v_a_1741_,
                    v___x_1745_,
                );
                v___x_1755_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1755_, 0, v___x_1753_);
                leanh::lean_ctor_set(v___x_1755_, 1, v___x_1754_);
                leanh::lean_inc(v___y_1747_);
                v___x_1756_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1756_, 0, v___y_1747_);
                leanh::lean_ctor_set(v___x_1756_, 1, v___x_1755_);
                v___x_1757_ = 0;
                v___x_1758_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1758_, 0, v___x_1756_);
                leanh::lean_ctor_set_uint8(
                    v___x_1758_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1757_,
                );
                v___x_1759_ = l_Repr_addAppParen(v___x_1758_, v_prec_1703_);
                return v___x_1759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instReprTaggedText_repr(
    mut v_00_u03b1_1765_: *mut leanh::LeanObject,
    mut v_inst_1766_: *mut leanh::LeanObject,
    mut v_x_1767_: *mut leanh::LeanObject,
    mut v_prec_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1769_ =
        l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_1766_, v_x_1767_, v_prec_1768_);
    return v___x_1769_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText_repr___boxed(
    mut v_00_u03b1_1770_: *mut leanh::LeanObject,
    mut v_inst_1771_: *mut leanh::LeanObject,
    mut v_x_1772_: *mut leanh::LeanObject,
    mut v_prec_1773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1774_ = l_Lean_Widget_instReprTaggedText_repr(
        v_00_u03b1_1770_,
        v_inst_1771_,
        v_x_1772_,
        v_prec_1773_,
    );
    leanh::lean_dec(v_prec_1773_);
    return v_res_1774_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText___redArg(
    mut v_inst_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1776_ = leanh::lean_alloc_closure(
        l_Lean_Widget_instReprTaggedText_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_1776_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1776_, 1, v_inst_1775_);
    return v___x_1776_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText(
    mut v_00_u03b1_1777_: *mut leanh::LeanObject,
    mut v_inst_1778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1779_ = leanh::lean_alloc_closure(
        l_Lean_Widget_instReprTaggedText_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_1779_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1779_, 1, v_inst_1778_);
    return v___x_1779_;
}
pub unsafe fn l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(
    mut v_inst_1789_: *mut leanh::LeanObject,
    mut v_json_1790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_a_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut v_a_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut v_a_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1863_: u8 = 0;
    let mut v_a_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1867_: u8 = 0;
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v_a_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localinst_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1894_: u8 = 0;
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1898_: u8 = 0;
    let mut v_a_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_json_1790_);
                v___x_1791_ = l_Lean_Json_getTag_x3f(v_json_1790_);
                if leanh::lean_obj_tag(v___x_1791_) == 0 {
                    leanh::lean_dec(v_json_1790_);
                    leanh::lean_dec_ref(v_inst_1789_);
                    v___x_1792_ =
                        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1;
                    return v___x_1792_;
                } else {
                    v_val_1793_ = leanh::lean_ctor_get(v___x_1791_, 0);
                    v_isSharedCheck_1910_ = (!leanh::lean_is_exclusive(v___x_1791_)) as u8;
                    if v_isSharedCheck_1910_ == 0 {
                        v___x_1795_ = v___x_1791_;
                        v_isShared_1796_ = v_isSharedCheck_1910_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1793_);
                        leanh::lean_dec(v___x_1791_);
                        v___x_1795_ = leanh::lean_box(0);
                        v_isShared_1796_ = v_isSharedCheck_1910_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1797_ = leanh::lean_box(0);
                v___x_1798_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2;
                v___x_1799_ = lean_string_dec_eq(v_val_1793_, v___x_1798_);
                if v___x_1799_ == 0 {
                    v___x_1800_ =
                        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3;
                    v___x_1801_ = lean_string_dec_eq(v_val_1793_, v___x_1800_);
                    if v___x_1801_ == 0 {
                        leanh::lean_del_object(v___x_1795_);
                        v___x_1802_ =
                            l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4;
                        v___x_1803_ = lean_string_dec_eq(v_val_1793_, v___x_1802_);
                        leanh::lean_dec(v_val_1793_);
                        if v___x_1803_ == 0 {
                            leanh::lean_dec(v_json_1790_);
                            leanh::lean_dec_ref(v_inst_1789_);
                            v___x_1804_ =
                                l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6;
                            return v___x_1804_;
                        } else {
                            v___x_1805_ = leanh::lean_unsigned_to_nat(2);
                            v___x_1806_ = leanh::lean_box(0);
                            v___x_1807_ = l_Lean_Json_parseCtorFields(
                                v_json_1790_,
                                v___x_1802_,
                                v___x_1805_,
                                v___x_1806_,
                            );
                            if leanh::lean_obj_tag(v___x_1807_) == 0 {
                                leanh::lean_dec_ref(v_inst_1789_);
                                v_a_1808_ = leanh::lean_ctor_get(v___x_1807_, 0);
                                v_isSharedCheck_1815_ =
                                    (!leanh::lean_is_exclusive(v___x_1807_)) as u8;
                                if v_isSharedCheck_1815_ == 0 {
                                    v___x_1810_ = v___x_1807_;
                                    v_isShared_1811_ = v_isSharedCheck_1815_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1808_);
                                    leanh::lean_dec(v___x_1807_);
                                    v___x_1810_ = leanh::lean_box(0);
                                    v_isShared_1811_ = v_isSharedCheck_1815_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_1816_ = leanh::lean_ctor_get(v___x_1807_, 0);
                                leanh::lean_inc(v_a_1816_);
                                leanh::lean_dec_ref_known(v___x_1807_, 1);
                                v___x_1817_ = leanh::lean_unsigned_to_nat(0);
                                v___x_1818_ =
                                    lean_array_get_borrowed(v___x_1797_, v_a_1816_, v___x_1817_);
                                leanh::lean_inc_ref(v_inst_1789_);
                                leanh::lean_inc(v___x_1818_);
                                v___x_1819_ = leanh::lean_apply_1(v_inst_1789_, v___x_1818_);
                                if leanh::lean_obj_tag(v___x_1819_) == 0 {
                                    leanh::lean_dec(v_a_1816_);
                                    leanh::lean_dec_ref(v_inst_1789_);
                                    v_a_1820_ = leanh::lean_ctor_get(v___x_1819_, 0);
                                    v_isSharedCheck_1827_ =
                                        (!leanh::lean_is_exclusive(v___x_1819_)) as u8;
                                    if v_isSharedCheck_1827_ == 0 {
                                        v___x_1822_ = v___x_1819_;
                                        v_isShared_1823_ = v_isSharedCheck_1827_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1820_);
                                        leanh::lean_dec(v___x_1819_);
                                        v___x_1822_ = leanh::lean_box(0);
                                        v_isShared_1823_ = v_isSharedCheck_1827_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v_a_1828_ = leanh::lean_ctor_get(v___x_1819_, 0);
                                    leanh::lean_inc(v_a_1828_);
                                    leanh::lean_dec_ref_known(v___x_1819_, 1);
                                    v___x_1829_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_1830_ =
                                        lean_array_get(v___x_1797_, v_a_1816_, v___x_1829_);
                                    leanh::lean_dec(v_a_1816_);
                                    v___x_1831_ =
                                        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(
                                            v_inst_1789_,
                                            v___x_1830_,
                                        );
                                    if leanh::lean_obj_tag(v___x_1831_) == 0 {
                                        leanh::lean_dec(v_a_1828_);
                                        return v___x_1831_;
                                    } else {
                                        v_a_1832_ = leanh::lean_ctor_get(v___x_1831_, 0);
                                        v_isSharedCheck_1840_ =
                                            (!leanh::lean_is_exclusive(v___x_1831_)) as u8;
                                        if v_isSharedCheck_1840_ == 0 {
                                            v___x_1834_ = v___x_1831_;
                                            v_isShared_1835_ = v_isSharedCheck_1840_;
                                            state = 6;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1832_);
                                            leanh::lean_dec(v___x_1831_);
                                            v___x_1834_ = leanh::lean_box(0);
                                            v_isShared_1835_ = v_isSharedCheck_1840_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_1793_);
                        leanh::lean_dec_ref(v_inst_1789_);
                        v___x_1841_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1842_ = leanh::lean_box(0);
                        v___x_1843_ = l_Lean_Json_parseCtorFields(
                            v_json_1790_,
                            v___x_1800_,
                            v___x_1841_,
                            v___x_1842_,
                        );
                        if leanh::lean_obj_tag(v___x_1843_) == 0 {
                            leanh::lean_del_object(v___x_1795_);
                            v_a_1844_ = leanh::lean_ctor_get(v___x_1843_, 0);
                            v_isSharedCheck_1851_ =
                                (!leanh::lean_is_exclusive(v___x_1843_)) as u8;
                            if v_isSharedCheck_1851_ == 0 {
                                v___x_1846_ = v___x_1843_;
                                v_isShared_1847_ = v_isSharedCheck_1851_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1844_);
                                leanh::lean_dec(v___x_1843_);
                                v___x_1846_ = leanh::lean_box(0);
                                v_isShared_1847_ = v_isSharedCheck_1851_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_1852_ = leanh::lean_ctor_get(v___x_1843_, 0);
                            leanh::lean_inc(v_a_1852_);
                            leanh::lean_dec_ref_known(v___x_1843_, 1);
                            v___x_1853_ = leanh::lean_unsigned_to_nat(0);
                            v___x_1854_ = lean_array_get(v___x_1797_, v_a_1852_, v___x_1853_);
                            leanh::lean_dec(v_a_1852_);
                            v___x_1855_ = l_Lean_Json_getStr_x3f(v___x_1854_);
                            if leanh::lean_obj_tag(v___x_1855_) == 0 {
                                leanh::lean_del_object(v___x_1795_);
                                v_a_1856_ = leanh::lean_ctor_get(v___x_1855_, 0);
                                v_isSharedCheck_1863_ =
                                    (!leanh::lean_is_exclusive(v___x_1855_)) as u8;
                                if v_isSharedCheck_1863_ == 0 {
                                    v___x_1858_ = v___x_1855_;
                                    v_isShared_1859_ = v_isSharedCheck_1863_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1856_);
                                    leanh::lean_dec(v___x_1855_);
                                    v___x_1858_ = leanh::lean_box(0);
                                    v_isShared_1859_ = v_isSharedCheck_1863_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                v_a_1864_ = leanh::lean_ctor_get(v___x_1855_, 0);
                                v_isSharedCheck_1874_ =
                                    (!leanh::lean_is_exclusive(v___x_1855_)) as u8;
                                if v_isSharedCheck_1874_ == 0 {
                                    v___x_1866_ = v___x_1855_;
                                    v_isShared_1867_ = v_isSharedCheck_1874_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1864_);
                                    leanh::lean_dec(v___x_1855_);
                                    v___x_1866_ = leanh::lean_box(0);
                                    v_isShared_1867_ = v_isSharedCheck_1874_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_val_1793_);
                    v___x_1875_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1876_ = leanh::lean_box(0);
                    v___x_1877_ = l_Lean_Json_parseCtorFields(
                        v_json_1790_,
                        v___x_1798_,
                        v___x_1875_,
                        v___x_1876_,
                    );
                    if leanh::lean_obj_tag(v___x_1877_) == 0 {
                        leanh::lean_del_object(v___x_1795_);
                        leanh::lean_dec_ref(v_inst_1789_);
                        v_a_1878_ = leanh::lean_ctor_get(v___x_1877_, 0);
                        v_isSharedCheck_1885_ =
                            (!leanh::lean_is_exclusive(v___x_1877_)) as u8;
                        if v_isSharedCheck_1885_ == 0 {
                            v___x_1880_ = v___x_1877_;
                            v_isShared_1881_ = v_isSharedCheck_1885_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1878_);
                            leanh::lean_dec(v___x_1877_);
                            v___x_1880_ = leanh::lean_box(0);
                            v_isShared_1881_ = v_isSharedCheck_1885_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v_a_1886_ = leanh::lean_ctor_get(v___x_1877_, 0);
                        leanh::lean_inc(v_a_1886_);
                        leanh::lean_dec_ref_known(v___x_1877_, 1);
                        v_localinst_1887_ = leanh::lean_alloc_closure(
                            l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v_localinst_1887_, 0, v_inst_1789_);
                        v___x_1888_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1889_ = lean_array_get(v___x_1797_, v_a_1886_, v___x_1888_);
                        leanh::lean_dec(v_a_1886_);
                        v___x_1890_ = l_Array_fromJson_x3f___redArg(v_localinst_1887_, v___x_1889_);
                        if leanh::lean_obj_tag(v___x_1890_) == 0 {
                            leanh::lean_del_object(v___x_1795_);
                            v_a_1891_ = leanh::lean_ctor_get(v___x_1890_, 0);
                            v_isSharedCheck_1898_ =
                                (!leanh::lean_is_exclusive(v___x_1890_)) as u8;
                            if v_isSharedCheck_1898_ == 0 {
                                v___x_1893_ = v___x_1890_;
                                v_isShared_1894_ = v_isSharedCheck_1898_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1891_);
                                leanh::lean_dec(v___x_1890_);
                                v___x_1893_ = leanh::lean_box(0);
                                v_isShared_1894_ = v_isSharedCheck_1898_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v_a_1899_ = leanh::lean_ctor_get(v___x_1890_, 0);
                            v_isSharedCheck_1909_ =
                                (!leanh::lean_is_exclusive(v___x_1890_)) as u8;
                            if v_isSharedCheck_1909_ == 0 {
                                v___x_1901_ = v___x_1890_;
                                v_isShared_1902_ = v_isSharedCheck_1909_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1899_);
                                leanh::lean_dec(v___x_1890_);
                                v___x_1901_ = leanh::lean_box(0);
                                v_isShared_1902_ = v_isSharedCheck_1909_;
                                state = 19;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                if v_isShared_1811_ == 0 {
                    v___x_1813_ = v___x_1810_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1814_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
                    v___x_1813_ = v_reuseFailAlloc_1814_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1813_;
            }
            4 => {
                if v_isShared_1823_ == 0 {
                    v___x_1825_ = v___x_1822_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
                    v___x_1825_ = v_reuseFailAlloc_1826_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1825_;
            }
            6 => {
                v___x_1836_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1836_, 0, v_a_1828_);
                leanh::lean_ctor_set(v___x_1836_, 1, v_a_1832_);
                if v_isShared_1835_ == 0 {
                    leanh::lean_ctor_set(v___x_1834_, 0, v___x_1836_);
                    v___x_1838_ = v___x_1834_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
                    v___x_1838_ = v_reuseFailAlloc_1839_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1838_;
            }
            8 => {
                if v_isShared_1847_ == 0 {
                    v___x_1849_ = v___x_1846_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
                    v___x_1849_ = v_reuseFailAlloc_1850_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1849_;
            }
            10 => {
                if v_isShared_1859_ == 0 {
                    v___x_1861_ = v___x_1858_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
                    v___x_1861_ = v_reuseFailAlloc_1862_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1861_;
            }
            12 => {
                if v_isShared_1796_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1795_, 0);
                    leanh::lean_ctor_set(v___x_1795_, 0, v_a_1864_);
                    v___x_1869_ = v___x_1795_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1864_);
                    v___x_1869_ = v_reuseFailAlloc_1873_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_1867_ == 0 {
                    leanh::lean_ctor_set(v___x_1866_, 0, v___x_1869_);
                    v___x_1871_ = v___x_1866_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
                    v___x_1871_ = v_reuseFailAlloc_1872_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1871_;
            }
            15 => {
                if v_isShared_1881_ == 0 {
                    v___x_1883_ = v___x_1880_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
                    v___x_1883_ = v_reuseFailAlloc_1884_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1883_;
            }
            17 => {
                if v_isShared_1894_ == 0 {
                    v___x_1896_ = v___x_1893_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1897_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
                    v___x_1896_ = v_reuseFailAlloc_1897_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1896_;
            }
            19 => {
                if v_isShared_1796_ == 0 {
                    leanh::lean_ctor_set(v___x_1795_, 0, v_a_1899_);
                    v___x_1904_ = v___x_1795_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1899_);
                    v___x_1904_ = v_reuseFailAlloc_1908_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1902_ == 0 {
                    leanh::lean_ctor_set(v___x_1901_, 0, v___x_1904_);
                    v___x_1906_ = v___x_1901_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
                    v___x_1906_ = v_reuseFailAlloc_1907_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instFromJsonTaggedText_fromJson(
    mut v_00_u03b1_1911_: *mut leanh::LeanObject,
    mut v_inst_1912_: *mut leanh::LeanObject,
    mut v_json_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ =
        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_1912_, v_json_1913_);
    return v___x_1914_;
}
pub unsafe fn l_Lean_Widget_instFromJsonTaggedText___redArg(
    mut v_inst_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = leanh::lean_alloc_closure(
        l_Lean_Widget_instFromJsonTaggedText_fromJson as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1916_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1916_, 1, v_inst_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_Widget_instFromJsonTaggedText(
    mut v_00_u03b1_1917_: *mut leanh::LeanObject,
    mut v_inst_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = leanh::lean_alloc_closure(
        l_Lean_Widget_instFromJsonTaggedText_fromJson as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1919_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1919_, 1, v_inst_1918_);
    return v___x_1919_;
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText_toJson___redArg(
    mut v_inst_1920_: *mut leanh::LeanObject,
    mut v_x_1921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1934_: u8 = 0;
    let mut v_a_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localinst_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1921_) {
                0 => {
                    leanh::lean_dec_ref(v_inst_1920_);
                    v_a_1922_ = leanh::lean_ctor_get(v_x_1921_, 0);
                    v_isSharedCheck_1934_ = (!leanh::lean_is_exclusive(v_x_1921_)) as u8;
                    if v_isSharedCheck_1934_ == 0 {
                        v___x_1924_ = v_x_1921_;
                        v_isShared_1925_ = v_isSharedCheck_1934_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1922_);
                        leanh::lean_dec(v_x_1921_);
                        v___x_1924_ = leanh::lean_box(0);
                        v_isShared_1925_ = v_isSharedCheck_1934_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_1935_ = leanh::lean_ctor_get(v_x_1921_, 0);
                    leanh::lean_inc_ref(v_a_1935_);
                    leanh::lean_dec_ref_known(v_x_1921_, 1);
                    v_localinst_1936_ = leanh::lean_alloc_closure(
                        l_Lean_Widget_instToJsonTaggedText_toJson___redArg
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v_localinst_1936_, 0, v_inst_1920_);
                    v___x_1937_ =
                        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2;
                    v___x_1938_ = l_Array_toJson___redArg(v_localinst_1936_, v_a_1935_);
                    v___x_1939_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1939_, 0, v___x_1937_);
                    leanh::lean_ctor_set(v___x_1939_, 1, v___x_1938_);
                    v___x_1940_ = leanh::lean_box(0);
                    v___x_1941_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1941_, 0, v___x_1939_);
                    leanh::lean_ctor_set(v___x_1941_, 1, v___x_1940_);
                    v___x_1942_ = l_Lean_Json_mkObj(v___x_1941_);
                    leanh::lean_dec_ref_known(v___x_1941_, 2);
                    return v___x_1942_;
                }
                _ => {
                    v_a_1943_ = leanh::lean_ctor_get(v_x_1921_, 0);
                    v_a_1944_ = leanh::lean_ctor_get(v_x_1921_, 1);
                    v_isSharedCheck_1962_ = (!leanh::lean_is_exclusive(v_x_1921_)) as u8;
                    if v_isSharedCheck_1962_ == 0 {
                        v___x_1946_ = v_x_1921_;
                        v_isShared_1947_ = v_isSharedCheck_1962_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1944_);
                        leanh::lean_inc(v_a_1943_);
                        leanh::lean_dec(v_x_1921_);
                        v___x_1946_ = leanh::lean_box(0);
                        v_isShared_1947_ = v_isSharedCheck_1962_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1926_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3;
                if v_isShared_1925_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1924_, 3);
                    v___x_1928_ = v___x_1924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1933_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1922_);
                    v___x_1928_ = v_reuseFailAlloc_1933_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1929_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1929_, 0, v___x_1926_);
                leanh::lean_ctor_set(v___x_1929_, 1, v___x_1928_);
                v___x_1930_ = leanh::lean_box(0);
                v___x_1931_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1931_, 0, v___x_1929_);
                leanh::lean_ctor_set(v___x_1931_, 1, v___x_1930_);
                v___x_1932_ = l_Lean_Json_mkObj(v___x_1931_);
                leanh::lean_dec_ref_known(v___x_1931_, 2);
                return v___x_1932_;
            }
            3 => {
                v___x_1948_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4;
                leanh::lean_inc_ref(v_inst_1920_);
                v___x_1949_ = leanh::lean_apply_1(v_inst_1920_, v_a_1943_);
                v___x_1950_ =
                    l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_1920_, v_a_1944_);
                v___x_1951_ = leanh::lean_unsigned_to_nat(2);
                v___x_1952_ = lean_mk_empty_array_with_capacity(v___x_1951_);
                v___x_1953_ = lean_array_push(v___x_1952_, v___x_1949_);
                v___x_1954_ = lean_array_push(v___x_1953_, v___x_1950_);
                v___x_1955_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1955_, 0, v___x_1954_);
                if v_isShared_1947_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1946_, 0);
                    leanh::lean_ctor_set(v___x_1946_, 1, v___x_1955_);
                    leanh::lean_ctor_set(v___x_1946_, 0, v___x_1948_);
                    v___x_1957_ = v___x_1946_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1961_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1955_);
                    v___x_1957_ = v_reuseFailAlloc_1961_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1958_ = leanh::lean_box(0);
                v___x_1959_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1959_, 0, v___x_1957_);
                leanh::lean_ctor_set(v___x_1959_, 1, v___x_1958_);
                v___x_1960_ = l_Lean_Json_mkObj(v___x_1959_);
                leanh::lean_dec_ref_known(v___x_1959_, 2);
                return v___x_1960_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText_toJson(
    mut v_00_u03b1_1963_: *mut leanh::LeanObject,
    mut v_inst_1964_: *mut leanh::LeanObject,
    mut v_x_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1966_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_1964_, v_x_1965_);
    return v___x_1966_;
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText___redArg(
    mut v_inst_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1968_ = leanh::lean_alloc_closure(
        l_Lean_Widget_instToJsonTaggedText_toJson as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1968_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1968_, 1, v_inst_1967_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText(
    mut v_00_u03b1_1969_: *mut leanh::LeanObject,
    mut v_inst_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1971_ = leanh::lean_alloc_closure(
        l_Lean_Widget_instToJsonTaggedText_toJson as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1971_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1971_, 1, v_inst_1970_);
    return v___x_1971_;
}
pub unsafe fn l_Lean_Widget_TaggedText_appendText___redArg(
    mut v_s_u2080_1972_: *mut leanh::LeanObject,
    mut v_x_1973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut v_a_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1973_) {
                0 => {
                    v_a_1974_ = leanh::lean_ctor_get(v_x_1973_, 0);
                    v_isSharedCheck_1982_ = (!leanh::lean_is_exclusive(v_x_1973_)) as u8;
                    if v_isSharedCheck_1982_ == 0 {
                        v___x_1976_ = v_x_1973_;
                        v_isShared_1977_ = v_isSharedCheck_1982_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1974_);
                        leanh::lean_dec(v_x_1973_);
                        v___x_1976_ = leanh::lean_box(0);
                        v_isShared_1977_ = v_isSharedCheck_1982_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_1983_ = leanh::lean_ctor_get(v_x_1973_, 0);
                    v_isSharedCheck_2010_ = (!leanh::lean_is_exclusive(v_x_1973_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_1985_ = v_x_1973_;
                        v_isShared_1986_ = v_isSharedCheck_2010_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1983_);
                        leanh::lean_dec(v_x_1973_);
                        v___x_1985_ = leanh::lean_box(0);
                        v_isShared_1986_ = v_isSharedCheck_2010_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_2011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2011_, 0, v_s_u2080_1972_);
                    v___x_2012_ = leanh::lean_unsigned_to_nat(2);
                    v___x_2013_ = lean_mk_empty_array_with_capacity(v___x_2012_);
                    v___x_2014_ = lean_array_push(v___x_2013_, v_x_1973_);
                    v___x_2015_ = lean_array_push(v___x_2014_, v___x_2011_);
                    v___x_2016_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2016_, 0, v___x_2015_);
                    return v___x_2016_;
                }
            },
            1 => {
                v___x_1978_ = lean_string_append(v_a_1974_, v_s_u2080_1972_);
                leanh::lean_dec_ref(v_s_u2080_1972_);
                if v_isShared_1977_ == 0 {
                    leanh::lean_ctor_set(v___x_1976_, 0, v___x_1978_);
                    v___x_1980_ = v___x_1976_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
                    v___x_1980_ = v_reuseFailAlloc_1981_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1980_;
            }
            3 => {
                v___x_1987_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0_once),
                    _init_l_Lean_Widget_instInhabitedTaggedText___closed__0,
                );
                v___x_1988_ = lean_array_get_size(v_a_1983_);
                v___x_1989_ = leanh::lean_unsigned_to_nat(1);
                v___x_1990_ = lean_nat_sub(v___x_1988_, v___x_1989_);
                v___x_1991_ = lean_array_get(v___x_1987_, v_a_1983_, v___x_1990_);
                if leanh::lean_obj_tag(v___x_1991_) == 0 {
                    v_a_1992_ = leanh::lean_ctor_get(v___x_1991_, 0);
                    v_isSharedCheck_2004_ = (!leanh::lean_is_exclusive(v___x_1991_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v___x_1994_ = v___x_1991_;
                        v_isShared_1995_ = v_isSharedCheck_2004_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1992_);
                        leanh::lean_dec(v___x_1991_);
                        v___x_1994_ = leanh::lean_box(0);
                        v_isShared_1995_ = v_isSharedCheck_2004_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1991_);
                    leanh::lean_dec(v___x_1990_);
                    if v_isShared_1986_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1985_, 0);
                        leanh::lean_ctor_set(v___x_1985_, 0, v_s_u2080_1972_);
                        v___x_2006_ = v___x_1985_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2009_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_s_u2080_1972_);
                        v___x_2006_ = v_reuseFailAlloc_2009_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1996_ = lean_string_append(v_a_1992_, v_s_u2080_1972_);
                leanh::lean_dec_ref(v_s_u2080_1972_);
                if v_isShared_1995_ == 0 {
                    leanh::lean_ctor_set(v___x_1994_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1994_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1996_);
                    v___x_1998_ = v_reuseFailAlloc_2003_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1999_ = lean_array_set(v_a_1983_, v___x_1990_, v___x_1998_);
                leanh::lean_dec(v___x_1990_);
                if v_isShared_1986_ == 0 {
                    leanh::lean_ctor_set(v___x_1985_, 0, v___x_1999_);
                    v___x_2001_ = v___x_1985_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
                    v___x_2001_ = v_reuseFailAlloc_2002_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2001_;
            }
            7 => {
                v___x_2007_ = lean_array_push(v_a_1983_, v___x_2006_);
                v___x_2008_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2008_, 0, v___x_2007_);
                return v___x_2008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_appendText(
    mut v_00_u03b1_2017_: *mut leanh::LeanObject,
    mut v_s_u2080_2018_: *mut leanh::LeanObject,
    mut v_x_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_u2080_2018_, v_x_2019_);
    return v___x_2020_;
}
pub unsafe fn l_Lean_Widget_TaggedText_appendTag___redArg(
    mut v_acc_2021_: *mut leanh::LeanObject,
    mut v_t_u2080_2022_: *mut leanh::LeanObject,
    mut v_a_u2080_2023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2041_: u8 = 0;
    let mut v_a_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: u8 = 0;
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_acc_2021_) {
                1 => {
                    v_a_2032_ = leanh::lean_ctor_get(v_acc_2021_, 0);
                    v_isSharedCheck_2041_ = (!leanh::lean_is_exclusive(v_acc_2021_)) as u8;
                    if v_isSharedCheck_2041_ == 0 {
                        v___x_2034_ = v_acc_2021_;
                        v_isShared_2035_ = v_isSharedCheck_2041_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2032_);
                        leanh::lean_dec(v_acc_2021_);
                        v___x_2034_ = leanh::lean_box(0);
                        v_isShared_2035_ = v_isSharedCheck_2041_;
                        state = 2;
                        continue;
                    }
                }
                0 => {
                    v_a_2042_ = leanh::lean_ctor_get(v_acc_2021_, 0);
                    v___x_2043_ = l_Lean_Widget_instInhabitedTaggedText_default___closed__0;
                    v___x_2044_ = lean_string_dec_eq(v_a_2042_, v___x_2043_);
                    if v___x_2044_ == 0 {
                        v_a_2025_ = v_acc_2021_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_acc_2021_, 1);
                        v___x_2045_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2045_, 0, v_t_u2080_2022_);
                        leanh::lean_ctor_set(v___x_2045_, 1, v_a_u2080_2023_);
                        return v___x_2045_;
                    }
                }
                _ => {
                    v_a_2025_ = v_acc_2021_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_2026_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2026_, 0, v_t_u2080_2022_);
                leanh::lean_ctor_set(v___x_2026_, 1, v_a_u2080_2023_);
                v___x_2027_ = leanh::lean_unsigned_to_nat(2);
                v___x_2028_ = lean_mk_empty_array_with_capacity(v___x_2027_);
                v___x_2029_ = lean_array_push(v___x_2028_, v_a_2025_);
                v___x_2030_ = lean_array_push(v___x_2029_, v___x_2026_);
                v___x_2031_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2031_, 0, v___x_2030_);
                return v___x_2031_;
            }
            2 => {
                v___x_2036_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2036_, 0, v_t_u2080_2022_);
                leanh::lean_ctor_set(v___x_2036_, 1, v_a_u2080_2023_);
                v___x_2037_ = lean_array_push(v_a_2032_, v___x_2036_);
                if v_isShared_2035_ == 0 {
                    leanh::lean_ctor_set(v___x_2034_, 0, v___x_2037_);
                    v___x_2039_ = v___x_2034_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
                    v___x_2039_ = v_reuseFailAlloc_2040_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_appendTag(
    mut v_00_u03b1_2046_: *mut leanh::LeanObject,
    mut v_acc_2047_: *mut leanh::LeanObject,
    mut v_t_u2080_2048_: *mut leanh::LeanObject,
    mut v_a_u2080_2049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ =
        l_Lean_Widget_TaggedText_appendTag___redArg(v_acc_2047_, v_t_u2080_2048_, v_a_u2080_2049_);
    return v___x_2050_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(
    mut v_f_2051_: *mut leanh::LeanObject,
    mut v_sz_2052_: usize,
    mut v_i_2053_: usize,
    mut v_bs_2054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2055_: u8 = 0;
    let mut v_v_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: usize = 0;
    let mut v___x_2061_: usize = 0;
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2055_ = lean_usize_dec_lt(v_i_2053_, v_sz_2052_);
                if v___x_2055_ == 0 {
                    leanh::lean_dec(v_f_2051_);
                    return v_bs_2054_;
                } else {
                    v_v_2056_ = lean_array_uget(v_bs_2054_, v_i_2053_);
                    v___x_2057_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2058_ = lean_array_uset(v_bs_2054_, v_i_2053_, v___x_2057_);
                    leanh::lean_inc(v_f_2051_);
                    v___x_2059_ = l_Lean_Widget_TaggedText_map___redArg(v_f_2051_, v_v_2056_);
                    v___x_2060_ = 1usize;
                    v___x_2061_ = lean_usize_add(v_i_2053_, v___x_2060_);
                    v___x_2062_ = lean_array_uset(v_bs_x27_2058_, v_i_2053_, v___x_2059_);
                    v_i_2053_ = v___x_2061_;
                    v_bs_2054_ = v___x_2062_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_map___redArg(
    mut v_f_2064_: *mut leanh::LeanObject,
    mut v_x_2065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut v_a_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v_sz_2078_: usize = 0;
    let mut v___x_2079_: usize = 0;
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_a_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2089_: u8 = 0;
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2065_) {
                0 => {
                    leanh::lean_dec(v_f_2064_);
                    v_a_2066_ = leanh::lean_ctor_get(v_x_2065_, 0);
                    v_isSharedCheck_2073_ = (!leanh::lean_is_exclusive(v_x_2065_)) as u8;
                    if v_isSharedCheck_2073_ == 0 {
                        v___x_2068_ = v_x_2065_;
                        v_isShared_2069_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2066_);
                        leanh::lean_dec(v_x_2065_);
                        v___x_2068_ = leanh::lean_box(0);
                        v_isShared_2069_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_2074_ = leanh::lean_ctor_get(v_x_2065_, 0);
                    v_isSharedCheck_2084_ = (!leanh::lean_is_exclusive(v_x_2065_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v___x_2076_ = v_x_2065_;
                        v_isShared_2077_ = v_isSharedCheck_2084_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2074_);
                        leanh::lean_dec(v_x_2065_);
                        v___x_2076_ = leanh::lean_box(0);
                        v_isShared_2077_ = v_isSharedCheck_2084_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_2085_ = leanh::lean_ctor_get(v_x_2065_, 0);
                    v_a_2086_ = leanh::lean_ctor_get(v_x_2065_, 1);
                    v_isSharedCheck_2095_ = (!leanh::lean_is_exclusive(v_x_2065_)) as u8;
                    if v_isSharedCheck_2095_ == 0 {
                        v___x_2088_ = v_x_2065_;
                        v_isShared_2089_ = v_isSharedCheck_2095_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2086_);
                        leanh::lean_inc(v_a_2085_);
                        leanh::lean_dec(v_x_2065_);
                        v___x_2088_ = leanh::lean_box(0);
                        v_isShared_2089_ = v_isSharedCheck_2095_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_2069_ == 0 {
                    v___x_2071_ = v___x_2068_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2072_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
                    v___x_2071_ = v_reuseFailAlloc_2072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2071_;
            }
            3 => {
                v_sz_2078_ = lean_array_size(v_a_2074_);
                v___x_2079_ = 0usize;
                v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_2064_, v_sz_2078_, v___x_2079_, v_a_2074_);
                if v_isShared_2077_ == 0 {
                    leanh::lean_ctor_set(v___x_2076_, 0, v___x_2080_);
                    v___x_2082_ = v___x_2076_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
                    v___x_2082_ = v_reuseFailAlloc_2083_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2082_;
            }
            5 => {
                leanh::lean_inc(v_f_2064_);
                v___x_2090_ = leanh::lean_apply_1(v_f_2064_, v_a_2085_);
                v___x_2091_ = l_Lean_Widget_TaggedText_map___redArg(v_f_2064_, v_a_2086_);
                if v_isShared_2089_ == 0 {
                    leanh::lean_ctor_set(v___x_2088_, 1, v___x_2091_);
                    leanh::lean_ctor_set(v___x_2088_, 0, v___x_2090_);
                    v___x_2093_ = v___x_2088_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2094_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2091_);
                    v___x_2093_ = v_reuseFailAlloc_2094_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg___boxed(
    mut v_f_2096_: *mut leanh::LeanObject,
    mut v_sz_2097_: *mut leanh::LeanObject,
    mut v_i_2098_: *mut leanh::LeanObject,
    mut v_bs_2099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2100_: usize = 0;
    let mut v_i_boxed_2101_: usize = 0;
    let mut v_res_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2100_ = leanh::lean_unbox_usize(v_sz_2097_);
    leanh::lean_dec(v_sz_2097_);
    v_i_boxed_2101_ = leanh::lean_unbox_usize(v_i_2098_);
    leanh::lean_dec(v_i_2098_);
    v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_2096_, v_sz_boxed_2100_, v_i_boxed_2101_, v_bs_2099_);
    return v_res_2102_;
}
pub unsafe fn l_Lean_Widget_TaggedText_map(
    mut v_00_u03b1_2103_: *mut leanh::LeanObject,
    mut v_00_u03b2_2104_: *mut leanh::LeanObject,
    mut v_f_2105_: *mut leanh::LeanObject,
    mut v_x_2106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2107_ = l_Lean_Widget_TaggedText_map___redArg(v_f_2105_, v_x_2106_);
    return v___x_2107_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(
    mut v_00_u03b1_2108_: *mut leanh::LeanObject,
    mut v_00_u03b2_2109_: *mut leanh::LeanObject,
    mut v_f_2110_: *mut leanh::LeanObject,
    mut v_sz_2111_: usize,
    mut v_i_2112_: usize,
    mut v_bs_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_2110_, v_sz_2111_, v_i_2112_, v_bs_2113_);
    return v___x_2114_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___boxed(
    mut v_00_u03b1_2115_: *mut leanh::LeanObject,
    mut v_00_u03b2_2116_: *mut leanh::LeanObject,
    mut v_f_2117_: *mut leanh::LeanObject,
    mut v_sz_2118_: *mut leanh::LeanObject,
    mut v_i_2119_: *mut leanh::LeanObject,
    mut v_bs_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2121_: usize = 0;
    let mut v_i_boxed_2122_: usize = 0;
    let mut v_res_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2121_ = leanh::lean_unbox_usize(v_sz_2118_);
    leanh::lean_dec(v_sz_2118_);
    v_i_boxed_2122_ = leanh::lean_unbox_usize(v_i_2119_);
    leanh::lean_dec(v_i_2119_);
    v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(v_00_u03b1_2115_, v_00_u03b2_2116_, v_f_2117_, v_sz_boxed_2121_, v_i_boxed_2122_, v_bs_2120_);
    return v_res_2123_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___redArg___lam__0(
    mut v_toPure_2124_: *mut leanh::LeanObject,
    mut v_____do__lift_2125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2126_, 0, v_____do__lift_2125_);
    v___x_2127_ =
        leanh::lean_apply_2(v_toPure_2124_, leanh::lean_box(0), v___x_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___redArg___lam__1(
    mut v_____do__lift_2128_: *mut leanh::LeanObject,
    mut v_toPure_2129_: *mut leanh::LeanObject,
    mut v_____do__lift_2130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2131_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2131_, 0, v_____do__lift_2128_);
    leanh::lean_ctor_set(v___x_2131_, 1, v_____do__lift_2130_);
    v___x_2132_ =
        leanh::lean_apply_2(v_toPure_2129_, leanh::lean_box(0), v___x_2131_);
    return v___x_2132_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___redArg(
    mut v_inst_2133_: *mut leanh::LeanObject,
    mut v_f_2134_: *mut leanh::LeanObject,
    mut v_x_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2141_: u8 = 0;
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v_toApplicative_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2153_: usize = 0;
    let mut v___x_2154_: usize = 0;
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2135_) {
                0 => {
                    v_toApplicative_2136_ = leanh::lean_ctor_get(v_inst_2133_, 0);
                    leanh::lean_inc_ref(v_toApplicative_2136_);
                    leanh::lean_dec(v_f_2134_);
                    leanh::lean_dec_ref(v_inst_2133_);
                    v_toPure_2137_ = leanh::lean_ctor_get(v_toApplicative_2136_, 1);
                    leanh::lean_inc(v_toPure_2137_);
                    leanh::lean_dec_ref(v_toApplicative_2136_);
                    v_a_2138_ = leanh::lean_ctor_get(v_x_2135_, 0);
                    v_isSharedCheck_2146_ = (!leanh::lean_is_exclusive(v_x_2135_)) as u8;
                    if v_isSharedCheck_2146_ == 0 {
                        v___x_2140_ = v_x_2135_;
                        v_isShared_2141_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2138_);
                        leanh::lean_dec(v_x_2135_);
                        v___x_2140_ = leanh::lean_box(0);
                        v_isShared_2141_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_toApplicative_2147_ = leanh::lean_ctor_get(v_inst_2133_, 0);
                    v_toBind_2148_ = leanh::lean_ctor_get(v_inst_2133_, 1);
                    leanh::lean_inc(v_toBind_2148_);
                    v_toPure_2149_ = leanh::lean_ctor_get(v_toApplicative_2147_, 1);
                    v_a_2150_ = leanh::lean_ctor_get(v_x_2135_, 0);
                    leanh::lean_inc_ref(v_a_2150_);
                    leanh::lean_dec_ref_known(v_x_2135_, 1);
                    leanh::lean_inc(v_toPure_2149_);
                    v___f_2151_ = leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_mapM___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2151_, 0, v_toPure_2149_);
                    leanh::lean_inc_ref(v_inst_2133_);
                    v___x_2152_ = leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_mapM___redArg as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___x_2152_, 0, v_inst_2133_);
                    leanh::lean_closure_set(v___x_2152_, 1, v_f_2134_);
                    v_sz_2153_ = lean_array_size(v_a_2150_);
                    v___x_2154_ = 0usize;
                    v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_2133_,
                        v___x_2152_,
                        v_sz_2153_,
                        v___x_2154_,
                        v_a_2150_,
                    );
                    v___x_2156_ = leanh::lean_apply_4(
                        v_toBind_2148_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2155_,
                        v___f_2151_,
                    );
                    return v___x_2156_;
                }
                _ => {
                    v_toApplicative_2157_ = leanh::lean_ctor_get(v_inst_2133_, 0);
                    v_toBind_2158_ = leanh::lean_ctor_get(v_inst_2133_, 1);
                    leanh::lean_inc_n(v_toBind_2158_, 2);
                    v_toPure_2159_ = leanh::lean_ctor_get(v_toApplicative_2157_, 1);
                    leanh::lean_inc(v_toPure_2159_);
                    v_a_2160_ = leanh::lean_ctor_get(v_x_2135_, 0);
                    leanh::lean_inc(v_a_2160_);
                    v_a_2161_ = leanh::lean_ctor_get(v_x_2135_, 1);
                    leanh::lean_inc_ref(v_a_2161_);
                    leanh::lean_dec_ref_known(v_x_2135_, 2);
                    leanh::lean_inc(v_f_2134_);
                    v___f_2162_ = leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_mapM___redArg___lam__2 as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    leanh::lean_closure_set(v___f_2162_, 0, v_toPure_2159_);
                    leanh::lean_closure_set(v___f_2162_, 1, v_inst_2133_);
                    leanh::lean_closure_set(v___f_2162_, 2, v_f_2134_);
                    leanh::lean_closure_set(v___f_2162_, 3, v_a_2161_);
                    leanh::lean_closure_set(v___f_2162_, 4, v_toBind_2158_);
                    v___x_2163_ = leanh::lean_apply_1(v_f_2134_, v_a_2160_);
                    v___x_2164_ = leanh::lean_apply_4(
                        v_toBind_2158_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2163_,
                        v___f_2162_,
                    );
                    return v___x_2164_;
                }
            },
            1 => {
                if v_isShared_2141_ == 0 {
                    v___x_2143_ = v___x_2140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2145_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2138_);
                    v___x_2143_ = v_reuseFailAlloc_2145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2144_ = leanh::lean_apply_2(
                    v_toPure_2137_,
                    leanh::lean_box(0),
                    v___x_2143_,
                );
                return v___x_2144_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___redArg___lam__2(
    mut v_toPure_2165_: *mut leanh::LeanObject,
    mut v_inst_2166_: *mut leanh::LeanObject,
    mut v_f_2167_: *mut leanh::LeanObject,
    mut v_a_2168_: *mut leanh::LeanObject,
    mut v_toBind_2169_: *mut leanh::LeanObject,
    mut v_____do__lift_2170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2171_ = leanh::lean_alloc_closure(
        l_Lean_Widget_TaggedText_mapM___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2171_, 0, v_____do__lift_2170_);
    leanh::lean_closure_set(v___f_2171_, 1, v_toPure_2165_);
    v___x_2172_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_2166_, v_f_2167_, v_a_2168_);
    v___x_2173_ = leanh::lean_apply_4(
        v_toBind_2169_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2172_,
        v___f_2171_,
    );
    return v___x_2173_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM(
    mut v_m_2174_: *mut leanh::LeanObject,
    mut v_00_u03b1_2175_: *mut leanh::LeanObject,
    mut v_00_u03b2_2176_: *mut leanh::LeanObject,
    mut v_inst_2177_: *mut leanh::LeanObject,
    mut v_f_2178_: *mut leanh::LeanObject,
    mut v_x_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_2177_, v_f_2178_, v_x_2179_);
    return v___x_2180_;
}
pub unsafe fn l_Lean_Widget_TaggedText_forM___redArg___lam__1(
    mut v_inst_2181_: *mut leanh::LeanObject,
    mut v_f_2182_: *mut leanh::LeanObject,
    mut v_a_2183_: *mut leanh::LeanObject,
    mut v_____r_2184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2185_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_2181_, v_f_2182_, v_a_2183_);
    return v___x_2185_;
}
pub unsafe fn l_Lean_Widget_TaggedText_forM___redArg(
    mut v_inst_2186_: *mut leanh::LeanObject,
    mut v_f_2187_: *mut leanh::LeanObject,
    mut v_x_2188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2188_) {
        0 => {
            let mut v_toApplicative_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_2189_ = leanh::lean_ctor_get(v_inst_2186_, 0);
            leanh::lean_inc_ref(v_toApplicative_2189_);
            leanh::lean_dec_ref_known(v_x_2188_, 1);
            leanh::lean_dec(v_f_2187_);
            leanh::lean_dec_ref(v_inst_2186_);
            v_toPure_2190_ = leanh::lean_ctor_get(v_toApplicative_2189_, 1);
            leanh::lean_inc(v_toPure_2190_);
            leanh::lean_dec_ref(v_toApplicative_2189_);
            v___x_2191_ = leanh::lean_box(0);
            v___x_2192_ =
                leanh::lean_apply_2(v_toPure_2190_, leanh::lean_box(0), v___x_2191_);
            return v___x_2192_;
        }
        1 => {
            let mut v_toApplicative_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2199_: u8 = 0;
            v_toApplicative_2193_ = leanh::lean_ctor_get(v_inst_2186_, 0);
            v_toPure_2194_ = leanh::lean_ctor_get(v_toApplicative_2193_, 1);
            v_a_2195_ = leanh::lean_ctor_get(v_x_2188_, 0);
            leanh::lean_inc_ref(v_a_2195_);
            leanh::lean_dec_ref_known(v_x_2188_, 1);
            v___x_2196_ = leanh::lean_unsigned_to_nat(0);
            v___x_2197_ = lean_array_get_size(v_a_2195_);
            v___x_2198_ = leanh::lean_box(0);
            v___x_2199_ = lean_nat_dec_lt(v___x_2196_, v___x_2197_);
            if v___x_2199_ == 0 {
                let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_toPure_2194_);
                leanh::lean_dec_ref(v_a_2195_);
                leanh::lean_dec(v_f_2187_);
                leanh::lean_dec_ref(v_inst_2186_);
                v___x_2200_ = leanh::lean_apply_2(
                    v_toPure_2194_,
                    leanh::lean_box(0),
                    v___x_2198_,
                );
                return v___x_2200_;
            } else {
                let mut v___f_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2202_: u8 = 0;
                leanh::lean_inc_ref(v_inst_2186_);
                v___f_2201_ = leanh::lean_alloc_closure(
                    l_Lean_Widget_TaggedText_forM___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_2201_, 0, v_inst_2186_);
                leanh::lean_closure_set(v___f_2201_, 1, v_f_2187_);
                v___x_2202_ = lean_nat_dec_le(v___x_2197_, v___x_2197_);
                if v___x_2202_ == 0 {
                    if v___x_2199_ == 0 {
                        let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_inc(v_toPure_2194_);
                        leanh::lean_dec_ref(v___f_2201_);
                        leanh::lean_dec_ref(v_a_2195_);
                        leanh::lean_dec_ref(v_inst_2186_);
                        v___x_2203_ = leanh::lean_apply_2(
                            v_toPure_2194_,
                            leanh::lean_box(0),
                            v___x_2198_,
                        );
                        return v___x_2203_;
                    } else {
                        let mut v___x_2204_: usize = 0;
                        let mut v___x_2205_: usize = 0;
                        let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_2204_ = 0usize;
                        v___x_2205_ = lean_usize_of_nat(v___x_2197_);
                        v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_inst_2186_,
                            v___f_2201_,
                            v_a_2195_,
                            v___x_2204_,
                            v___x_2205_,
                            v___x_2198_,
                        );
                        return v___x_2206_;
                    }
                } else {
                    let mut v___x_2207_: usize = 0;
                    let mut v___x_2208_: usize = 0;
                    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2207_ = 0usize;
                    v___x_2208_ = lean_usize_of_nat(v___x_2197_);
                    v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_2186_,
                        v___f_2201_,
                        v_a_2195_,
                        v___x_2207_,
                        v___x_2208_,
                        v___x_2198_,
                    );
                    return v___x_2209_;
                }
            }
        }
        _ => {
            let mut v_toBind_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toBind_2210_ = leanh::lean_ctor_get(v_inst_2186_, 1);
            leanh::lean_inc(v_toBind_2210_);
            v_a_2211_ = leanh::lean_ctor_get(v_x_2188_, 0);
            leanh::lean_inc(v_a_2211_);
            v_a_2212_ = leanh::lean_ctor_get(v_x_2188_, 1);
            leanh::lean_inc_ref_n(v_a_2212_, 2);
            leanh::lean_dec_ref_known(v_x_2188_, 2);
            leanh::lean_inc(v_f_2187_);
            v___f_2213_ = leanh::lean_alloc_closure(
                l_Lean_Widget_TaggedText_forM___redArg___lam__1 as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_2213_, 0, v_inst_2186_);
            leanh::lean_closure_set(v___f_2213_, 1, v_f_2187_);
            leanh::lean_closure_set(v___f_2213_, 2, v_a_2212_);
            v___x_2214_ = leanh::lean_apply_2(v_f_2187_, v_a_2211_, v_a_2212_);
            v___x_2215_ = leanh::lean_apply_4(
                v_toBind_2210_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2214_,
                v___f_2213_,
            );
            return v___x_2215_;
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_forM___redArg___lam__0(
    mut v_inst_2216_: *mut leanh::LeanObject,
    mut v_f_2217_: *mut leanh::LeanObject,
    mut v_x_2218_: *mut leanh::LeanObject,
    mut v___y_2219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2220_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_2216_, v_f_2217_, v___y_2219_);
    return v___x_2220_;
}
pub unsafe fn l_Lean_Widget_TaggedText_forM(
    mut v_m_2221_: *mut leanh::LeanObject,
    mut v_00_u03b1_2222_: *mut leanh::LeanObject,
    mut v_inst_2223_: *mut leanh::LeanObject,
    mut v_f_2224_: *mut leanh::LeanObject,
    mut v_x_2225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2226_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_2223_, v_f_2224_, v_x_2225_);
    return v___x_2226_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(
    mut v_f_2227_: *mut leanh::LeanObject,
    mut v_sz_2228_: usize,
    mut v_i_2229_: usize,
    mut v_bs_2230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2231_: u8 = 0;
    let mut v_v_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: usize = 0;
    let mut v___x_2237_: usize = 0;
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2231_ = lean_usize_dec_lt(v_i_2229_, v_sz_2228_);
                if v___x_2231_ == 0 {
                    leanh::lean_dec_ref(v_f_2227_);
                    return v_bs_2230_;
                } else {
                    v_v_2232_ = lean_array_uget(v_bs_2230_, v_i_2229_);
                    v___x_2233_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2234_ = lean_array_uset(v_bs_2230_, v_i_2229_, v___x_2233_);
                    leanh::lean_inc_ref(v_f_2227_);
                    v___x_2235_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_2227_, v_v_2232_);
                    v___x_2236_ = 1usize;
                    v___x_2237_ = lean_usize_add(v_i_2229_, v___x_2236_);
                    v___x_2238_ = lean_array_uset(v_bs_x27_2234_, v_i_2229_, v___x_2235_);
                    v_i_2229_ = v___x_2237_;
                    v_bs_2230_ = v___x_2238_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_rewrite___redArg(
    mut v_f_2240_: *mut leanh::LeanObject,
    mut v_x_2241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_a_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2253_: u8 = 0;
    let mut v_sz_2254_: usize = 0;
    let mut v___x_2255_: usize = 0;
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v_a_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2241_) {
                0 => {
                    leanh::lean_dec_ref(v_f_2240_);
                    v_a_2242_ = leanh::lean_ctor_get(v_x_2241_, 0);
                    v_isSharedCheck_2249_ = (!leanh::lean_is_exclusive(v_x_2241_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v___x_2244_ = v_x_2241_;
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2242_);
                        leanh::lean_dec(v_x_2241_);
                        v___x_2244_ = leanh::lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_2250_ = leanh::lean_ctor_get(v_x_2241_, 0);
                    v_isSharedCheck_2260_ = (!leanh::lean_is_exclusive(v_x_2241_)) as u8;
                    if v_isSharedCheck_2260_ == 0 {
                        v___x_2252_ = v_x_2241_;
                        v_isShared_2253_ = v_isSharedCheck_2260_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2250_);
                        leanh::lean_dec(v_x_2241_);
                        v___x_2252_ = leanh::lean_box(0);
                        v_isShared_2253_ = v_isSharedCheck_2260_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_2261_ = leanh::lean_ctor_get(v_x_2241_, 0);
                    leanh::lean_inc(v_a_2261_);
                    v_a_2262_ = leanh::lean_ctor_get(v_x_2241_, 1);
                    leanh::lean_inc_ref(v_a_2262_);
                    leanh::lean_dec_ref_known(v_x_2241_, 2);
                    v___x_2263_ = leanh::lean_apply_2(v_f_2240_, v_a_2261_, v_a_2262_);
                    return v___x_2263_;
                }
            },
            1 => {
                if v_isShared_2245_ == 0 {
                    v___x_2247_ = v___x_2244_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
                    v___x_2247_ = v_reuseFailAlloc_2248_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2247_;
            }
            3 => {
                v_sz_2254_ = lean_array_size(v_a_2250_);
                v___x_2255_ = 0usize;
                v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_2240_, v_sz_2254_, v___x_2255_, v_a_2250_);
                if v_isShared_2253_ == 0 {
                    leanh::lean_ctor_set(v___x_2252_, 0, v___x_2256_);
                    v___x_2258_ = v___x_2252_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
                    v___x_2258_ = v_reuseFailAlloc_2259_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg___boxed(
    mut v_f_2264_: *mut leanh::LeanObject,
    mut v_sz_2265_: *mut leanh::LeanObject,
    mut v_i_2266_: *mut leanh::LeanObject,
    mut v_bs_2267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2268_: usize = 0;
    let mut v_i_boxed_2269_: usize = 0;
    let mut v_res_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2268_ = leanh::lean_unbox_usize(v_sz_2265_);
    leanh::lean_dec(v_sz_2265_);
    v_i_boxed_2269_ = leanh::lean_unbox_usize(v_i_2266_);
    leanh::lean_dec(v_i_2266_);
    v_res_2270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_2264_, v_sz_boxed_2268_, v_i_boxed_2269_, v_bs_2267_);
    return v_res_2270_;
}
pub unsafe fn l_Lean_Widget_TaggedText_rewrite(
    mut v_00_u03b1_2271_: *mut leanh::LeanObject,
    mut v_00_u03b2_2272_: *mut leanh::LeanObject,
    mut v_f_2273_: *mut leanh::LeanObject,
    mut v_x_2274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_2273_, v_x_2274_);
    return v___x_2275_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(
    mut v_00_u03b1_2276_: *mut leanh::LeanObject,
    mut v_00_u03b2_2277_: *mut leanh::LeanObject,
    mut v_f_2278_: *mut leanh::LeanObject,
    mut v_sz_2279_: usize,
    mut v_i_2280_: usize,
    mut v_bs_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_2278_, v_sz_2279_, v_i_2280_, v_bs_2281_);
    return v___x_2282_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___boxed(
    mut v_00_u03b1_2283_: *mut leanh::LeanObject,
    mut v_00_u03b2_2284_: *mut leanh::LeanObject,
    mut v_f_2285_: *mut leanh::LeanObject,
    mut v_sz_2286_: *mut leanh::LeanObject,
    mut v_i_2287_: *mut leanh::LeanObject,
    mut v_bs_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2289_: usize = 0;
    let mut v_i_boxed_2290_: usize = 0;
    let mut v_res_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2289_ = leanh::lean_unbox_usize(v_sz_2286_);
    leanh::lean_dec(v_sz_2286_);
    v_i_boxed_2290_ = leanh::lean_unbox_usize(v_i_2287_);
    leanh::lean_dec(v_i_2287_);
    v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(v_00_u03b1_2283_, v_00_u03b2_2284_, v_f_2285_, v_sz_boxed_2289_, v_i_boxed_2290_, v_bs_2288_);
    return v_res_2291_;
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM___redArg(
    mut v_inst_2292_: *mut leanh::LeanObject,
    mut v_f_2293_: *mut leanh::LeanObject,
    mut v_x_2294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2305_: u8 = 0;
    let mut v_toApplicative_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2312_: usize = 0;
    let mut v___x_2313_: usize = 0;
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2294_) {
                0 => {
                    v_toApplicative_2295_ = leanh::lean_ctor_get(v_inst_2292_, 0);
                    leanh::lean_inc_ref(v_toApplicative_2295_);
                    leanh::lean_dec(v_f_2293_);
                    leanh::lean_dec_ref(v_inst_2292_);
                    v_toPure_2296_ = leanh::lean_ctor_get(v_toApplicative_2295_, 1);
                    leanh::lean_inc(v_toPure_2296_);
                    leanh::lean_dec_ref(v_toApplicative_2295_);
                    v_a_2297_ = leanh::lean_ctor_get(v_x_2294_, 0);
                    v_isSharedCheck_2305_ = (!leanh::lean_is_exclusive(v_x_2294_)) as u8;
                    if v_isSharedCheck_2305_ == 0 {
                        v___x_2299_ = v_x_2294_;
                        v_isShared_2300_ = v_isSharedCheck_2305_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2297_);
                        leanh::lean_dec(v_x_2294_);
                        v___x_2299_ = leanh::lean_box(0);
                        v_isShared_2300_ = v_isSharedCheck_2305_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_toApplicative_2306_ = leanh::lean_ctor_get(v_inst_2292_, 0);
                    v_toBind_2307_ = leanh::lean_ctor_get(v_inst_2292_, 1);
                    leanh::lean_inc(v_toBind_2307_);
                    v_toPure_2308_ = leanh::lean_ctor_get(v_toApplicative_2306_, 1);
                    v_a_2309_ = leanh::lean_ctor_get(v_x_2294_, 0);
                    leanh::lean_inc_ref(v_a_2309_);
                    leanh::lean_dec_ref_known(v_x_2294_, 1);
                    leanh::lean_inc(v_toPure_2308_);
                    v___f_2310_ = leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_mapM___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2310_, 0, v_toPure_2308_);
                    leanh::lean_inc_ref(v_inst_2292_);
                    v___x_2311_ = leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_rewriteM___redArg as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___x_2311_, 0, v_inst_2292_);
                    leanh::lean_closure_set(v___x_2311_, 1, v_f_2293_);
                    v_sz_2312_ = lean_array_size(v_a_2309_);
                    v___x_2313_ = 0usize;
                    v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_2292_,
                        v___x_2311_,
                        v_sz_2312_,
                        v___x_2313_,
                        v_a_2309_,
                    );
                    v___x_2315_ = leanh::lean_apply_4(
                        v_toBind_2307_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2314_,
                        v___f_2310_,
                    );
                    return v___x_2315_;
                }
                _ => {
                    leanh::lean_dec_ref(v_inst_2292_);
                    v_a_2316_ = leanh::lean_ctor_get(v_x_2294_, 0);
                    leanh::lean_inc(v_a_2316_);
                    v_a_2317_ = leanh::lean_ctor_get(v_x_2294_, 1);
                    leanh::lean_inc_ref(v_a_2317_);
                    leanh::lean_dec_ref_known(v_x_2294_, 2);
                    v___x_2318_ = leanh::lean_apply_2(v_f_2293_, v_a_2316_, v_a_2317_);
                    return v___x_2318_;
                }
            },
            1 => {
                if v_isShared_2300_ == 0 {
                    v___x_2302_ = v___x_2299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2304_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2297_);
                    v___x_2302_ = v_reuseFailAlloc_2304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2303_ = leanh::lean_apply_2(
                    v_toPure_2296_,
                    leanh::lean_box(0),
                    v___x_2302_,
                );
                return v___x_2303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM(
    mut v_m_2319_: *mut leanh::LeanObject,
    mut v_00_u03b1_2320_: *mut leanh::LeanObject,
    mut v_00_u03b2_2321_: *mut leanh::LeanObject,
    mut v_inst_2322_: *mut leanh::LeanObject,
    mut v_f_2323_: *mut leanh::LeanObject,
    mut v_x_2324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2325_ = l_Lean_Widget_TaggedText_rewriteM___redArg(v_inst_2322_, v_f_2323_, v_x_2324_);
    return v___x_2325_;
}
pub unsafe fn l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0(
    mut v_inst_2326_: *mut leanh::LeanObject,
    mut v___x_2327_: *mut leanh::LeanObject,
    mut v___x_2328_: *mut leanh::LeanObject,
    mut v_a_2329_: *mut leanh::LeanObject,
    mut v___y_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rpcEncode_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641__overap_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2338_: u8 = 0;
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rpcEncode_2331_ = leanh::lean_ctor_get(v_inst_2326_, 0);
                leanh::lean_inc_ref(v_rpcEncode_2331_);
                leanh::lean_dec_ref(v_inst_2326_);
                v___x_641__overap_2332_ = l_Lean_Widget_TaggedText_mapM___redArg(
                    v___x_2327_,
                    v_rpcEncode_2331_,
                    v_a_2329_,
                );
                v___x_2333_ = leanh::lean_apply_1(v___x_641__overap_2332_, v___y_2330_);
                v_fst_2334_ = leanh::lean_ctor_get(v___x_2333_, 0);
                v_snd_2335_ = leanh::lean_ctor_get(v___x_2333_, 1);
                v_isSharedCheck_2343_ = (!leanh::lean_is_exclusive(v___x_2333_)) as u8;
                if v_isSharedCheck_2343_ == 0 {
                    v___x_2337_ = v___x_2333_;
                    v_isShared_2338_ = v_isSharedCheck_2343_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2335_);
                    leanh::lean_inc(v_fst_2334_);
                    leanh::lean_dec(v___x_2333_);
                    v___x_2337_ = leanh::lean_box(0);
                    v_isShared_2338_ = v_isSharedCheck_2343_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2339_ =
                    l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v___x_2328_, v_fst_2334_);
                if v_isShared_2338_ == 0 {
                    leanh::lean_ctor_set(v___x_2337_, 0, v___x_2339_);
                    v___x_2341_ = v___x_2337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_snd_2335_);
                    v___x_2341_ = v_reuseFailAlloc_2342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(
    mut v___f_2344_: *mut leanh::LeanObject,
    mut v_inst_2345_: *mut leanh::LeanObject,
    mut v___x_2346_: *mut leanh::LeanObject,
    mut v_a_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2353_: u8 = 0;
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut v_a_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rpcDecode_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654__overap_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2349_ =
                    l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v___f_2344_, v_a_2347_);
                if leanh::lean_obj_tag(v___x_2349_) == 0 {
                    leanh::lean_dec_ref(v___x_2346_);
                    leanh::lean_dec_ref(v_inst_2345_);
                    v_a_2350_ = leanh::lean_ctor_get(v___x_2349_, 0);
                    v_isSharedCheck_2357_ = (!leanh::lean_is_exclusive(v___x_2349_)) as u8;
                    if v_isSharedCheck_2357_ == 0 {
                        v___x_2352_ = v___x_2349_;
                        v_isShared_2353_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2350_);
                        leanh::lean_dec(v___x_2349_);
                        v___x_2352_ = leanh::lean_box(0);
                        v_isShared_2353_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2358_ = leanh::lean_ctor_get(v___x_2349_, 0);
                    leanh::lean_inc(v_a_2358_);
                    leanh::lean_dec_ref_known(v___x_2349_, 1);
                    v_rpcDecode_2359_ = leanh::lean_ctor_get(v_inst_2345_, 1);
                    leanh::lean_inc_ref(v_rpcDecode_2359_);
                    leanh::lean_dec_ref(v_inst_2345_);
                    v___x_654__overap_2360_ = l_Lean_Widget_TaggedText_mapM___redArg(
                        v___x_2346_,
                        v_rpcDecode_2359_,
                        v_a_2358_,
                    );
                    leanh::lean_inc_ref(v___y_2348_);
                    v___x_2361_ = leanh::lean_apply_1(v___x_654__overap_2360_, v___y_2348_);
                    return v___x_2361_;
                }
            }
            1 => {
                if v_isShared_2353_ == 0 {
                    v___x_2355_ = v___x_2352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2356_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
                    v___x_2355_ = v_reuseFailAlloc_2356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed(
    mut v___f_2362_: *mut leanh::LeanObject,
    mut v_inst_2363_: *mut leanh::LeanObject,
    mut v___x_2364_: *mut leanh::LeanObject,
    mut v_a_2365_: *mut leanh::LeanObject,
    mut v___y_2366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2367_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(
        v___f_2362_,
        v_inst_2363_,
        v___x_2364_,
        v_a_2365_,
        v___y_2366_,
    );
    leanh::lean_dec_ref(v___y_2366_);
    return v_res_2367_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9;
    v___x_2415_ = l_ReaderT_instMonad___redArg(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___f_2417_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2417_, 0, v___x_2416_);
    return v___f_2417_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2418_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___f_2419_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2419_, 0, v___x_2418_);
    return v___f_2419_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___f_2421_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2421_, 0, v___x_2420_);
    return v___f_2421_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2422_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___f_2423_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2423_, 0, v___x_2422_);
    return v___f_2423_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___x_2425_ = leanh::lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    leanh::lean_closure_set(v___x_2425_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2425_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2425_, 2, v___x_2424_);
    return v___x_2425_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27()
-> *mut leanh::LeanObject {
    let mut v___f_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2426_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22,
    );
    v___x_2427_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26,
    );
    v___x_2428_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2428_, 0, v___x_2427_);
    leanh::lean_ctor_set(v___x_2428_, 1, v___f_2426_);
    return v___x_2428_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___x_2430_ = leanh::lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2430_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2430_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2430_, 2, v___x_2429_);
    return v___x_2430_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29()
-> *mut leanh::LeanObject {
    let mut v___f_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2431_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25,
    );
    v___f_2432_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24,
    );
    v___f_2433_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23,
    );
    v___x_2434_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28,
    );
    v___x_2435_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27,
    );
    v___x_2436_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2436_, 0, v___x_2435_);
    leanh::lean_ctor_set(v___x_2436_, 1, v___x_2434_);
    leanh::lean_ctor_set(v___x_2436_, 2, v___f_2433_);
    leanh::lean_ctor_set(v___x_2436_, 3, v___f_2432_);
    leanh::lean_ctor_set(v___x_2436_, 4, v___f_2431_);
    return v___x_2436_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___x_2438_ = leanh::lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    leanh::lean_closure_set(v___x_2438_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2438_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2438_, 2, v___x_2437_);
    return v___x_2438_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2439_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30,
    );
    v___x_2440_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29,
    );
    v___x_2441_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2441_, 0, v___x_2440_);
    leanh::lean_ctor_set(v___x_2441_, 1, v___x_2439_);
    return v___x_2441_;
}
pub unsafe fn l_Lean_Widget_TaggedText_instRpcEncodable___redArg(
    mut v_inst_2443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19;
    v___x_2445_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20;
    leanh::lean_inc_ref(v_inst_2443_);
    v___f_2446_ = leanh::lean_alloc_closure(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_2446_, 0, v_inst_2443_);
    leanh::lean_closure_set(v___f_2446_, 1, v___x_2444_);
    leanh::lean_closure_set(v___f_2446_, 2, v___x_2445_);
    v___x_2447_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31,
    );
    v___f_2448_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32;
    v___f_2449_ = leanh::lean_alloc_closure(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_2449_, 0, v___f_2448_);
    leanh::lean_closure_set(v___f_2449_, 1, v_inst_2443_);
    leanh::lean_closure_set(v___f_2449_, 2, v___x_2447_);
    v___x_2450_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2450_, 0, v___f_2446_);
    leanh::lean_ctor_set(v___x_2450_, 1, v___f_2449_);
    return v___x_2450_;
}
pub unsafe fn l_Lean_Widget_TaggedText_instRpcEncodable(
    mut v_00_u03b1_2451_: *mut leanh::LeanObject,
    mut v_inst_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg(v_inst_2452_);
    return v___x_2453_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0(
    mut v_s_2462_: *mut leanh::LeanObject,
    mut v___y_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_out_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2464_ = leanh::lean_ctor_get(v___y_2463_, 0);
                v_tagStack_2465_ = leanh::lean_ctor_get(v___y_2463_, 1);
                v_column_2466_ = leanh::lean_ctor_get(v___y_2463_, 2);
                v_isSharedCheck_2478_ = (!leanh::lean_is_exclusive(v___y_2463_)) as u8;
                if v_isSharedCheck_2478_ == 0 {
                    v___x_2468_ = v___y_2463_;
                    v_isShared_2469_ = v_isSharedCheck_2478_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_column_2466_);
                    leanh::lean_inc(v_tagStack_2465_);
                    leanh::lean_inc(v_out_2464_);
                    leanh::lean_dec(v___y_2463_);
                    v___x_2468_ = leanh::lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2478_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2470_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_s_2462_);
                v___x_2471_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_2462_, v_out_2464_);
                v___x_2472_ = lean_string_length(v_s_2462_);
                leanh::lean_dec_ref(v_s_2462_);
                v___x_2473_ = lean_nat_add(v_column_2466_, v___x_2472_);
                leanh::lean_dec(v_column_2466_);
                if v_isShared_2469_ == 0 {
                    leanh::lean_ctor_set(v___x_2468_, 2, v___x_2473_);
                    leanh::lean_ctor_set(v___x_2468_, 0, v___x_2471_);
                    v___x_2475_ = v___x_2468_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2477_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_tagStack_2465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 2, v___x_2473_);
                    v___x_2475_ = v_reuseFailAlloc_2477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2476_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2476_, 0, v___x_2470_);
                leanh::lean_ctor_set(v___x_2476_, 1, v___x_2475_);
                return v___x_2476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(
    mut v___x_2479_: u32,
    mut v_s_2480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = lean_string_push(v_s_2480_, v___x_2479_);
    return v___x_2481_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed(
    mut v___x_2482_: *mut leanh::LeanObject,
    mut v_s_2483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_827__boxed_2484_: u32 = 0;
    let mut v_res_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_827__boxed_2484_ = leanh::lean_unbox_uint32(v___x_2482_);
    leanh::lean_dec(v___x_2482_);
    v_res_2485_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(v___x_827__boxed_2484_, v_s_2483_);
    return v_res_2485_;
}
pub unsafe fn _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_2487_: u32 = 0;
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2487_ = 32;
    v___x_2488_ = leanh::lean_box_uint32(v___x_2487_);
    return v___x_2488_;
}
pub unsafe fn _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1;
    v___f_2490_ = leanh::lean_alloc_closure(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_2490_, 0, v___x_2489_);
    return v___f_2490_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2(
    mut v_indent_2491_: *mut leanh::LeanObject,
    mut v___y_2492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_out_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut v_unused_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2493_ = leanh::lean_ctor_get(v___y_2492_, 0);
                v_tagStack_2494_ = leanh::lean_ctor_get(v___y_2492_, 1);
                v_isSharedCheck_2507_ = (!leanh::lean_is_exclusive(v___y_2492_)) as u8;
                if v_isSharedCheck_2507_ == 0 {
                    v_unused_2508_ = leanh::lean_ctor_get(v___y_2492_, 2);
                    leanh::lean_dec(v_unused_2508_);
                    v___x_2496_ = v___y_2492_;
                    v_isShared_2497_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tagStack_2494_);
                    leanh::lean_inc(v_out_2493_);
                    leanh::lean_dec(v___y_2492_);
                    v___x_2496_ = leanh::lean_box(0);
                    v_isShared_2497_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2498_ = leanh::lean_box(0);
                v___x_2499_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                v___f_2500_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once), _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1);
                leanh::lean_inc(v_indent_2491_);
                v___x_2501_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(
                    leanh::lean_box(0),
                    v___f_2500_,
                    v_indent_2491_,
                    v___x_2499_,
                );
                v___x_2502_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2501_, v_out_2493_);
                if v_isShared_2497_ == 0 {
                    leanh::lean_ctor_set(v___x_2496_, 2, v_indent_2491_);
                    leanh::lean_ctor_set(v___x_2496_, 0, v___x_2502_);
                    v___x_2504_ = v___x_2496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2506_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_tagStack_2494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 2, v_indent_2491_);
                    v___x_2504_ = v_reuseFailAlloc_2506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2505_, 0, v___x_2498_);
                leanh::lean_ctor_set(v___x_2505_, 1, v___x_2504_);
                return v___x_2505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(
    mut v_____do__lift_2509_: *mut leanh::LeanObject,
    mut v___y_2510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_column_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_column_2511_ = leanh::lean_ctor_get(v_____do__lift_2509_, 2);
    leanh::lean_inc(v_column_2511_);
    v___x_2512_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2512_, 0, v_column_2511_);
    leanh::lean_ctor_set(v___x_2512_, 1, v___y_2510_);
    return v___x_2512_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed(
    mut v_____do__lift_2513_: *mut leanh::LeanObject,
    mut v___y_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(v_____do__lift_2513_, v___y_2514_);
    leanh::lean_dec_ref(v_____do__lift_2513_);
    return v_res_2515_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4(
    mut v_n_2516_: *mut leanh::LeanObject,
    mut v___y_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_out_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2523_: u8 = 0;
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2518_ = leanh::lean_ctor_get(v___y_2517_, 0);
                v_tagStack_2519_ = leanh::lean_ctor_get(v___y_2517_, 1);
                v_column_2520_ = leanh::lean_ctor_get(v___y_2517_, 2);
                v_isSharedCheck_2533_ = (!leanh::lean_is_exclusive(v___y_2517_)) as u8;
                if v_isSharedCheck_2533_ == 0 {
                    v___x_2522_ = v___y_2517_;
                    v_isShared_2523_ = v_isSharedCheck_2533_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_column_2520_);
                    leanh::lean_inc(v_tagStack_2519_);
                    leanh::lean_inc(v_out_2518_);
                    leanh::lean_dec(v___y_2517_);
                    v___x_2522_ = leanh::lean_box(0);
                    v_isShared_2523_ = v_isSharedCheck_2533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2524_ = leanh::lean_box(0);
                v___x_2525_ = l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0;
                leanh::lean_inc(v_column_2520_);
                v___x_2526_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2526_, 0, v_column_2520_);
                leanh::lean_ctor_set(v___x_2526_, 1, v_out_2518_);
                v___x_2527_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2527_, 0, v_n_2516_);
                leanh::lean_ctor_set(v___x_2527_, 1, v___x_2526_);
                v___x_2528_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2528_, 0, v___x_2527_);
                leanh::lean_ctor_set(v___x_2528_, 1, v_tagStack_2519_);
                if v_isShared_2523_ == 0 {
                    leanh::lean_ctor_set(v___x_2522_, 1, v___x_2528_);
                    leanh::lean_ctor_set(v___x_2522_, 0, v___x_2525_);
                    v___x_2530_ = v___x_2522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2525_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_column_2520_);
                    v___x_2530_ = v_reuseFailAlloc_2532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2531_, 0, v___x_2524_);
                leanh::lean_ctor_set(v___x_2531_, 1, v___x_2530_);
                return v___x_2531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5(
    mut v_acc_2534_: *mut leanh::LeanObject,
    mut v_x_2535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2536_ = leanh::lean_ctor_get(v_x_2535_, 1);
                leanh::lean_inc(v_snd_2536_);
                v_fst_2537_ = leanh::lean_ctor_get(v_x_2535_, 0);
                leanh::lean_inc(v_fst_2537_);
                leanh::lean_dec_ref(v_x_2535_);
                v_fst_2538_ = leanh::lean_ctor_get(v_snd_2536_, 0);
                v_snd_2539_ = leanh::lean_ctor_get(v_snd_2536_, 1);
                v_isSharedCheck_2547_ = (!leanh::lean_is_exclusive(v_snd_2536_)) as u8;
                if v_isSharedCheck_2547_ == 0 {
                    v___x_2541_ = v_snd_2536_;
                    v_isShared_2542_ = v_isSharedCheck_2547_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2539_);
                    leanh::lean_inc(v_fst_2538_);
                    leanh::lean_dec(v_snd_2536_);
                    v___x_2541_ = leanh::lean_box(0);
                    v_isShared_2542_ = v_isSharedCheck_2547_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2542_ == 0 {
                    leanh::lean_ctor_set(v___x_2541_, 1, v_fst_2538_);
                    leanh::lean_ctor_set(v___x_2541_, 0, v_fst_2537_);
                    v___x_2544_ = v___x_2541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2546_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_fst_2537_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_fst_2538_);
                    v___x_2544_ = v_reuseFailAlloc_2546_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2545_ = l_Lean_Widget_TaggedText_appendTag___redArg(
                    v_snd_2539_,
                    v___x_2544_,
                    v_acc_2534_,
                );
                return v___x_2545_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6(
    mut v___f_2550_: *mut leanh::LeanObject,
    mut v_n_2551_: *mut leanh::LeanObject,
    mut v___y_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_out_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2553_ = leanh::lean_ctor_get(v___y_2552_, 0);
                v_tagStack_2554_ = leanh::lean_ctor_get(v___y_2552_, 1);
                v_column_2555_ = leanh::lean_ctor_get(v___y_2552_, 2);
                v_isSharedCheck_2568_ = (!leanh::lean_is_exclusive(v___y_2552_)) as u8;
                if v_isSharedCheck_2568_ == 0 {
                    v___x_2557_ = v___y_2552_;
                    v_isShared_2558_ = v_isSharedCheck_2568_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_column_2555_);
                    leanh::lean_inc(v_tagStack_2554_);
                    leanh::lean_inc(v_out_2553_);
                    leanh::lean_dec(v___y_2552_);
                    v___x_2557_ = leanh::lean_box(0);
                    v_isShared_2558_ = v_isSharedCheck_2568_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2559_ = leanh::lean_box(0);
                v___x_2560_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                leanh::lean_inc(v_n_2551_);
                leanh::lean_inc(v_tagStack_2554_);
                v___x_2561_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    leanh::lean_box(0),
                    v_tagStack_2554_,
                    v_tagStack_2554_,
                    v_n_2551_,
                    v___x_2560_,
                );
                v___x_2562_ = l_List_drop___redArg(v_n_2551_, v_tagStack_2554_);
                leanh::lean_dec(v_tagStack_2554_);
                v_out_x27_2563_ = l_List_foldl___redArg(v___f_2550_, v_out_2553_, v___x_2561_);
                if v_isShared_2558_ == 0 {
                    leanh::lean_ctor_set(v___x_2557_, 1, v___x_2562_);
                    leanh::lean_ctor_set(v___x_2557_, 0, v_out_x27_2563_);
                    v___x_2565_ = v___x_2557_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_out_x27_2563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___x_2562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_column_2555_);
                    v___x_2565_ = v_reuseFailAlloc_2567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2566_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2566_, 0, v___x_2559_);
                leanh::lean_ctor_set(v___x_2566_, 1, v___x_2565_);
                return v___x_2566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(
    mut v_x_2589_: *mut leanh::LeanObject,
    mut v_x_2590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2592_: u8 = 0;
    let mut v___x_2593_: u32 = 0;
    let mut v_one_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2591_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2592_ = lean_nat_dec_eq(v_x_2589_, v_zero_2591_);
                if v_isZero_2592_ == 1 {
                    leanh::lean_dec(v_x_2589_);
                    return v_x_2590_;
                } else {
                    v___x_2593_ = 32;
                    v_one_2594_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2595_ = lean_nat_sub(v_x_2589_, v_one_2594_);
                    leanh::lean_dec(v_x_2589_);
                    v___x_2596_ = lean_string_push(v_x_2590_, v___x_2593_);
                    v_x_2589_ = v_n_2595_;
                    v_x_2590_ = v___x_2596_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(
    mut v_fla_2598_: *mut leanh::LeanObject,
    mut v_flb_2599_: u8,
    mut v_tail_2600_: *mut leanh::LeanObject,
    mut v_is_x27_2601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2602_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_2602_, 0, v_fla_2598_);
    leanh::lean_ctor_set(v___x_2602_, 1, v_is_x27_2601_);
    leanh::lean_ctor_set_uint8(
        v___x_2602_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_flb_2599_,
    );
    v___x_2603_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2603_, 0, v___x_2602_);
    leanh::lean_ctor_set(v___x_2603_, 1, v_tail_2600_);
    return v___x_2603_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(
    mut v_fla_2604_: *mut leanh::LeanObject,
    mut v_flb_2605_: *mut leanh::LeanObject,
    mut v_tail_2606_: *mut leanh::LeanObject,
    mut v_is_x27_2607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flb_6181__boxed_2608_: u8 = 0;
    let mut v_res_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flb_6181__boxed_2608_ = (leanh::lean_unbox(v_flb_2605_) as u8);
    v_res_2609_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2604_, v_flb_6181__boxed_2608_, v_tail_2606_, v_is_x27_2607_);
    return v_res_2609_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(
    mut v_flb_2610_: u8,
    mut v_items_2611_: *mut leanh::LeanObject,
    mut v_gs_2612_: *mut leanh::LeanObject,
    mut v_w_2613_: *mut leanh::LeanObject,
    mut v___y_2614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2616_: u8 = 0;
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: u8 = 0;
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundFlattenedHardLine_2632_: u8 = 0;
    let mut v_space_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: u8 = 0;
    let mut v___x_2635_: u8 = 0;
    let mut v_foundLine_2636_: u8 = 0;
    let mut v_space_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2639_: u8 = 0;
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2642_: u8 = 0;
    let mut v_foundFlattenedHardLine_2643_: u8 = 0;
    let mut v_space_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v___x_2653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_column_2621_ = leanh::lean_ctor_get(v___y_2614_, 2);
                v___x_2622_ = 0;
                v___x_2623_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_2610_, v___x_2622_);
                v___x_2624_ = leanh::lean_alloc_ctor(0, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_2624_, 0 as u32, v___x_2623_);
                leanh::lean_inc(v_items_2611_);
                v_g_2625_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v_g_2625_, 0, v___x_2624_);
                leanh::lean_ctor_set(v_g_2625_, 1, v_items_2611_);
                leanh::lean_ctor_set_uint8(
                    v_g_2625_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_flb_2610_,
                );
                v___x_2626_ = leanh::lean_box(0);
                v___x_2627_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2627_, 0, v_g_2625_);
                leanh::lean_ctor_set(v___x_2627_, 1, v___x_2626_);
                v___x_2628_ = lean_nat_sub(v_w_2613_, v_column_2621_);
                leanh::lean_inc(v___x_2628_);
                leanh::lean_inc(v_column_2621_);
                v_r_2629_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                    v___x_2627_,
                    v_column_2621_,
                    v___x_2628_,
                );
                v_foundLine_2636_ = leanh::lean_ctor_get_uint8(
                    v_r_2629_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_space_2637_ = leanh::lean_ctor_get(v_r_2629_, 0);
                leanh::lean_inc(v_space_2637_);
                v___x_2653_ = lean_nat_dec_lt(v___x_2628_, v_space_2637_);
                if v___x_2653_ == 0 {
                    v___y_2639_ = v_foundLine_2636_;
                    state = 3;
                    continue;
                } else {
                    v___y_2639_ = v___x_2653_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_2617_ = leanh::lean_alloc_ctor(0, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_2617_, 0 as u32, v___y_2616_);
                v___x_2618_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_2618_, 0, v___x_2617_);
                leanh::lean_ctor_set(v___x_2618_, 1, v_items_2611_);
                leanh::lean_ctor_set_uint8(
                    v___x_2618_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_flb_2610_,
                );
                v___x_2619_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2619_, 0, v___x_2618_);
                leanh::lean_ctor_set(v___x_2619_, 1, v_gs_2612_);
                v___x_2620_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2620_, 0, v___x_2619_);
                leanh::lean_ctor_set(v___x_2620_, 1, v___y_2614_);
                return v___x_2620_;
            }
            2 => {
                v_foundFlattenedHardLine_2632_ = leanh::lean_ctor_get_uint8(
                    v_r_2629_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                );
                leanh::lean_dec_ref(v_r_2629_);
                if v_foundFlattenedHardLine_2632_ == 0 {
                    v_space_2633_ = leanh::lean_ctor_get(v___y_2631_, 0);
                    leanh::lean_inc(v_space_2633_);
                    leanh::lean_dec_ref(v___y_2631_);
                    v___x_2634_ = lean_nat_dec_le(v_space_2633_, v___x_2628_);
                    leanh::lean_dec(v___x_2628_);
                    leanh::lean_dec(v_space_2633_);
                    v___y_2616_ = v___x_2634_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_2631_);
                    leanh::lean_dec(v___x_2628_);
                    v___x_2635_ = 0;
                    v___y_2616_ = v___x_2635_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2639_ == 0 {
                    v___x_2640_ = lean_nat_sub(v___x_2628_, v_space_2637_);
                    leanh::lean_inc(v_column_2621_);
                    leanh::lean_inc(v_gs_2612_);
                    v_r_u2082_2641_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                            v_gs_2612_,
                            v_column_2621_,
                            v___x_2640_,
                        );
                    v_foundLine_2642_ = leanh::lean_ctor_get_uint8(
                        v_r_u2082_2641_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_2643_ = leanh::lean_ctor_get_uint8(
                        v_r_u2082_2641_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_2644_ = leanh::lean_ctor_get(v_r_u2082_2641_, 0);
                    v_isSharedCheck_2652_ =
                        (!leanh::lean_is_exclusive(v_r_u2082_2641_)) as u8;
                    if v_isSharedCheck_2652_ == 0 {
                        v___x_2646_ = v_r_u2082_2641_;
                        v_isShared_2647_ = v_isSharedCheck_2652_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_space_2644_);
                        leanh::lean_dec(v_r_u2082_2641_);
                        v___x_2646_ = leanh::lean_box(0);
                        v_isShared_2647_ = v_isSharedCheck_2652_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_space_2637_);
                    leanh::lean_inc_ref(v_r_2629_);
                    v___y_2631_ = v_r_2629_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2648_ = lean_nat_add(v_space_2637_, v_space_2644_);
                leanh::lean_dec(v_space_2644_);
                leanh::lean_dec(v_space_2637_);
                if v_isShared_2647_ == 0 {
                    leanh::lean_ctor_set(v___x_2646_, 0, v___x_2648_);
                    v___x_2650_ = v___x_2646_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2651_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_foundLine_2642_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2651_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                        v_foundFlattenedHardLine_2643_,
                    );
                    v___x_2650_ = v_reuseFailAlloc_2651_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2631_ = v___x_2650_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4___boxed(
    mut v_flb_2654_: *mut leanh::LeanObject,
    mut v_items_2655_: *mut leanh::LeanObject,
    mut v_gs_2656_: *mut leanh::LeanObject,
    mut v_w_2657_: *mut leanh::LeanObject,
    mut v___y_2658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flb_boxed_2659_: u8 = 0;
    let mut v_res_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flb_boxed_2659_ = (leanh::lean_unbox(v_flb_2654_) as u8);
    v_res_2660_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_boxed_2659_, v_items_2655_, v_gs_2656_, v_w_2657_, v___y_2658_);
    leanh::lean_dec(v_w_2657_);
    return v_res_2660_;
}
pub unsafe fn l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(
    mut v_x_2661_: *mut leanh::LeanObject,
    mut v_x_2662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2662_) == 0 {
                    return v_x_2661_;
                } else {
                    v_head_2663_ = leanh::lean_ctor_get(v_x_2662_, 0);
                    leanh::lean_inc(v_head_2663_);
                    v_snd_2664_ = leanh::lean_ctor_get(v_head_2663_, 1);
                    leanh::lean_inc(v_snd_2664_);
                    v_tail_2665_ = leanh::lean_ctor_get(v_x_2662_, 1);
                    leanh::lean_inc(v_tail_2665_);
                    leanh::lean_dec_ref_known(v_x_2662_, 2);
                    v_fst_2666_ = leanh::lean_ctor_get(v_head_2663_, 0);
                    leanh::lean_inc(v_fst_2666_);
                    leanh::lean_dec(v_head_2663_);
                    v_fst_2667_ = leanh::lean_ctor_get(v_snd_2664_, 0);
                    v_snd_2668_ = leanh::lean_ctor_get(v_snd_2664_, 1);
                    v_isSharedCheck_2677_ = (!leanh::lean_is_exclusive(v_snd_2664_)) as u8;
                    if v_isSharedCheck_2677_ == 0 {
                        v___x_2670_ = v_snd_2664_;
                        v_isShared_2671_ = v_isSharedCheck_2677_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2668_);
                        leanh::lean_inc(v_fst_2667_);
                        leanh::lean_dec(v_snd_2664_);
                        v___x_2670_ = leanh::lean_box(0);
                        v_isShared_2671_ = v_isSharedCheck_2677_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2671_ == 0 {
                    leanh::lean_ctor_set(v___x_2670_, 1, v_fst_2667_);
                    leanh::lean_ctor_set(v___x_2670_, 0, v_fst_2666_);
                    v___x_2673_ = v___x_2670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2676_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_fst_2666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_fst_2667_);
                    v___x_2673_ = v_reuseFailAlloc_2676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2674_ = l_Lean_Widget_TaggedText_appendTag___redArg(
                    v_snd_2668_,
                    v___x_2673_,
                    v_x_2661_,
                );
                v_x_2661_ = v___x_2674_;
                v_x_2662_ = v_tail_2665_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2678_ = leanh::lean_box(0);
    v___x_2679_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19;
    v___x_2680_ = l_instInhabitedOfMonad___redArg(v___x_2679_, v___x_2678_);
    return v___x_2680_;
}
pub unsafe fn l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(
    mut v_msg_2681_: *mut leanh::LeanObject,
    mut v___y_2682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132__overap_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once), _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0);
    v___x_6132__overap_2684_ = lean_panic_fn_borrowed(v___x_2683_, v_msg_2681_);
    v___x_2685_ = leanh::lean_apply_1(v___x_6132__overap_2684_, v___y_2682_);
    return v___x_2685_;
}
pub unsafe fn _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2687_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0;
    v___x_2688_ = lean_string_length(v___x_2687_);
    return v___x_2688_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(
    mut v_w_2690_: *mut leanh::LeanObject,
    mut v_x_2691_: *mut leanh::LeanObject,
    mut v___y_2692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2703_: u8 = 0;
    let mut v_fla_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_flb_2705_: u8 = 0;
    let mut v_tail_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v_f_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeTags_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v_out_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: u8 = 0;
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u32 = 0;
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2755_: u8 = 0;
    let mut v___y_2757_: u8 = 0;
    let mut v_out_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2763_: u8 = 0;
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2773_: u8 = 0;
    let mut v_out_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2789_: u8 = 0;
    let mut v___x_2790_: u8 = 0;
    let mut v_out_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2809_: u8 = 0;
    let mut v_unused_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    let mut v_out_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v_unused_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fla_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: u8 = 0;
    let mut v_out_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2867_: u8 = 0;
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2882_: u8 = 0;
    let mut v_unused_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v_snd_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_force_2905_: u8 = 0;
    let mut v___x_2906_: u8 = 0;
    let mut v_a_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2910_: u8 = 0;
    let mut v___x_2911_: u32 = 0;
    let mut v_p_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: u8 = 0;
    let mut v_out_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2919_: u8 = 0;
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_is_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2949_: u8 = 0;
    let mut v_unused_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2956_: u8 = 0;
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2969_: u8 = 0;
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_indent_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_behavior_2998_: u8 = 0;
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_unused_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v_unused_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2691_) == 0 {
                    v___x_2693_ = leanh::lean_box(0);
                    v___x_2694_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2694_, 0, v___x_2693_);
                    leanh::lean_ctor_set(v___x_2694_, 1, v___y_2692_);
                    return v___x_2694_;
                } else {
                    v_head_2695_ = leanh::lean_ctor_get(v_x_2691_, 0);
                    v_items_2696_ = leanh::lean_ctor_get(v_head_2695_, 1);
                    leanh::lean_inc(v_items_2696_);
                    if leanh::lean_obj_tag(v_items_2696_) == 0 {
                        v_tail_2697_ = leanh::lean_ctor_get(v_x_2691_, 1);
                        leanh::lean_inc(v_tail_2697_);
                        leanh::lean_dec_ref_known(v_x_2691_, 2);
                        v_x_2691_ = v_tail_2697_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_head_2695_);
                        v_head_2699_ = leanh::lean_ctor_get(v_items_2696_, 0);
                        leanh::lean_inc(v_head_2699_);
                        v_tail_2700_ = leanh::lean_ctor_get(v_x_2691_, 1);
                        v_isSharedCheck_3051_ = (!leanh::lean_is_exclusive(v_x_2691_)) as u8;
                        if v_isSharedCheck_3051_ == 0 {
                            v_unused_3052_ = leanh::lean_ctor_get(v_x_2691_, 0);
                            leanh::lean_dec(v_unused_3052_);
                            v___x_2702_ = v_x_2691_;
                            v_isShared_2703_ = v_isSharedCheck_3051_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_2700_);
                            leanh::lean_dec(v_x_2691_);
                            v___x_2702_ = leanh::lean_box(0);
                            v_isShared_2703_ = v_isSharedCheck_3051_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fla_2704_ = leanh::lean_ctor_get(v_head_2695_, 0);
                leanh::lean_inc(v_fla_2704_);
                v_flb_2705_ = leanh::lean_ctor_get_uint8(
                    v_head_2695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                leanh::lean_dec(v_head_2695_);
                v_tail_2706_ = leanh::lean_ctor_get(v_items_2696_, 1);
                v_isSharedCheck_3049_ = (!leanh::lean_is_exclusive(v_items_2696_)) as u8;
                if v_isSharedCheck_3049_ == 0 {
                    v_unused_3050_ = leanh::lean_ctor_get(v_items_2696_, 0);
                    leanh::lean_dec(v_unused_3050_);
                    v___x_2708_ = v_items_2696_;
                    v_isShared_2709_ = v_isSharedCheck_3049_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_tail_2706_);
                    leanh::lean_dec(v_items_2696_);
                    v___x_2708_ = leanh::lean_box(0);
                    v_isShared_2709_ = v_isSharedCheck_3049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_f_2710_ = leanh::lean_ctor_get(v_head_2699_, 0);
                v_indent_2711_ = leanh::lean_ctor_get(v_head_2699_, 1);
                v_activeTags_2712_ = leanh::lean_ctor_get(v_head_2699_, 2);
                v_isSharedCheck_3048_ = (!leanh::lean_is_exclusive(v_head_2699_)) as u8;
                if v_isSharedCheck_3048_ == 0 {
                    v___x_2714_ = v_head_2699_;
                    v_isShared_2715_ = v_isSharedCheck_3048_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_activeTags_2712_);
                    leanh::lean_inc(v_indent_2711_);
                    leanh::lean_inc(v_f_2710_);
                    leanh::lean_dec(v_head_2699_);
                    v___x_2714_ = leanh::lean_box(0);
                    v_isShared_2715_ = v_isSharedCheck_3048_;
                    state = 3;
                    continue;
                }
            }
            3 => match leanh::lean_obj_tag(v_f_2710_) {
                0 => {
                    leanh::lean_del_object(v___x_2714_);
                    leanh::lean_dec(v_indent_2711_);
                    leanh::lean_del_object(v___x_2708_);
                    leanh::lean_del_object(v___x_2702_);
                    v_out_2774_ = leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_2775_ = leanh::lean_ctor_get(v___y_2692_, 1);
                    v_column_2776_ = leanh::lean_ctor_get(v___y_2692_, 2);
                    v_isSharedCheck_2789_ = (!leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_2789_ == 0 {
                        v___x_2778_ = v___y_2692_;
                        v_isShared_2779_ = v_isSharedCheck_2789_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_column_2776_);
                        leanh::lean_inc(v_tagStack_2775_);
                        leanh::lean_inc(v_out_2774_);
                        leanh::lean_dec(v___y_2692_);
                        v___x_2778_ = leanh::lean_box(0);
                        v_isShared_2779_ = v_isSharedCheck_2789_;
                        state = 11;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_2714_);
                    leanh::lean_del_object(v___x_2708_);
                    leanh::lean_del_object(v___x_2702_);
                    if v_flb_2705_ == 0 {
                        v___x_2790_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2704_);
                        if v___x_2790_ == 0 {
                            v_out_2791_ = leanh::lean_ctor_get(v___y_2692_, 0);
                            v_tagStack_2792_ = leanh::lean_ctor_get(v___y_2692_, 1);
                            v_isSharedCheck_2809_ =
                                (!leanh::lean_is_exclusive(v___y_2692_)) as u8;
                            if v_isSharedCheck_2809_ == 0 {
                                v_unused_2810_ = leanh::lean_ctor_get(v___y_2692_, 2);
                                leanh::lean_dec(v_unused_2810_);
                                v___x_2794_ = v___y_2692_;
                                v_isShared_2795_ = v_isSharedCheck_2809_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_tagStack_2792_);
                                leanh::lean_inc(v_out_2791_);
                                leanh::lean_dec(v___y_2692_);
                                v___x_2794_ = leanh::lean_box(0);
                                v_isShared_2795_ = v_isSharedCheck_2809_;
                                state = 13;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_indent_2711_);
                            v_out_2811_ = leanh::lean_ctor_get(v___y_2692_, 0);
                            v_tagStack_2812_ = leanh::lean_ctor_get(v___y_2692_, 1);
                            v_column_2813_ = leanh::lean_ctor_get(v___y_2692_, 2);
                            v_isSharedCheck_2830_ =
                                (!leanh::lean_is_exclusive(v___y_2692_)) as u8;
                            if v_isSharedCheck_2830_ == 0 {
                                v___x_2815_ = v___y_2692_;
                                v_isShared_2816_ = v_isSharedCheck_2830_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_column_2813_);
                                leanh::lean_inc(v_tagStack_2812_);
                                leanh::lean_inc(v_out_2811_);
                                leanh::lean_dec(v___y_2692_);
                                v___x_2815_ = leanh::lean_box(0);
                                v_isShared_2816_ = v_isSharedCheck_2830_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        v___x_2831_ = l_Int_toNat(v_indent_2711_);
                        leanh::lean_dec(v_indent_2711_);
                        v___x_2832_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2704_);
                        leanh::lean_dec(v_fla_2704_);
                        if v___x_2832_ == 0 {
                            v_out_2833_ = leanh::lean_ctor_get(v___y_2692_, 0);
                            v_tagStack_2834_ = leanh::lean_ctor_get(v___y_2692_, 1);
                            v_isSharedCheck_2852_ =
                                (!leanh::lean_is_exclusive(v___y_2692_)) as u8;
                            if v_isSharedCheck_2852_ == 0 {
                                v_unused_2853_ = leanh::lean_ctor_get(v___y_2692_, 2);
                                leanh::lean_dec(v_unused_2853_);
                                v___x_2836_ = v___y_2692_;
                                v_isShared_2837_ = v_isSharedCheck_2852_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_tagStack_2834_);
                                leanh::lean_inc(v_out_2833_);
                                leanh::lean_dec(v___y_2692_);
                                v___x_2836_ = leanh::lean_box(0);
                                v_isShared_2837_ = v_isSharedCheck_2852_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v___x_2854_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0;
                            v___x_2855_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once), _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1);
                            v___x_2856_ = lean_nat_sub(v_w_2690_, v___x_2855_);
                            leanh::lean_inc(v_tail_2700_);
                            leanh::lean_inc(v_tail_2706_);
                            v___x_2857_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_2705_, v_tail_2706_, v_tail_2700_, v___x_2856_, v___y_2692_);
                            leanh::lean_dec(v___x_2856_);
                            v_fst_2858_ = leanh::lean_ctor_get(v___x_2857_, 0);
                            leanh::lean_inc(v_fst_2858_);
                            if leanh::lean_obj_tag(v_fst_2858_) == 1 {
                                v_head_2859_ = leanh::lean_ctor_get(v_fst_2858_, 0);
                                v_snd_2860_ = leanh::lean_ctor_get(v___x_2857_, 1);
                                leanh::lean_inc(v_snd_2860_);
                                leanh::lean_dec_ref(v___x_2857_);
                                v_fla_2861_ = leanh::lean_ctor_get(v_head_2859_, 0);
                                v___x_2862_ =
                                    l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2861_);
                                if v___x_2862_ == 0 {
                                    leanh::lean_dec_ref_known(v_fst_2858_, 2);
                                    v_out_2863_ = leanh::lean_ctor_get(v_snd_2860_, 0);
                                    v_tagStack_2864_ = leanh::lean_ctor_get(v_snd_2860_, 1);
                                    v_isSharedCheck_2882_ =
                                        (!leanh::lean_is_exclusive(v_snd_2860_)) as u8;
                                    if v_isSharedCheck_2882_ == 0 {
                                        v_unused_2883_ =
                                            leanh::lean_ctor_get(v_snd_2860_, 2);
                                        leanh::lean_dec(v_unused_2883_);
                                        v___x_2866_ = v_snd_2860_;
                                        v_isShared_2867_ = v_isSharedCheck_2882_;
                                        state = 19;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_tagStack_2864_);
                                        leanh::lean_inc(v_out_2863_);
                                        leanh::lean_dec(v_snd_2860_);
                                        v___x_2866_ = leanh::lean_box(0);
                                        v_isShared_2867_ = v_isSharedCheck_2882_;
                                        state = 19;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_2831_);
                                    leanh::lean_dec(v_tail_2706_);
                                    leanh::lean_dec(v_tail_2700_);
                                    v_out_2884_ = leanh::lean_ctor_get(v_snd_2860_, 0);
                                    v_tagStack_2885_ = leanh::lean_ctor_get(v_snd_2860_, 1);
                                    v_column_2886_ = leanh::lean_ctor_get(v_snd_2860_, 2);
                                    v_isSharedCheck_2901_ =
                                        (!leanh::lean_is_exclusive(v_snd_2860_)) as u8;
                                    if v_isSharedCheck_2901_ == 0 {
                                        v___x_2888_ = v_snd_2860_;
                                        v_isShared_2889_ = v_isSharedCheck_2901_;
                                        state = 21;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_column_2886_);
                                        leanh::lean_inc(v_tagStack_2885_);
                                        leanh::lean_inc(v_out_2884_);
                                        leanh::lean_dec(v_snd_2860_);
                                        v___x_2888_ = leanh::lean_box(0);
                                        v_isShared_2889_ = v_isSharedCheck_2901_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_fst_2858_);
                                leanh::lean_dec(v___x_2831_);
                                leanh::lean_dec(v_activeTags_2712_);
                                leanh::lean_dec(v_tail_2706_);
                                leanh::lean_dec(v_tail_2700_);
                                v_snd_2902_ = leanh::lean_ctor_get(v___x_2857_, 1);
                                leanh::lean_inc(v_snd_2902_);
                                leanh::lean_dec_ref(v___x_2857_);
                                v___x_2903_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2;
                                v___x_2904_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(v___x_2903_, v_snd_2902_);
                                return v___x_2904_;
                            }
                        }
                    }
                }
                2 => {
                    leanh::lean_del_object(v___x_2714_);
                    leanh::lean_del_object(v___x_2708_);
                    leanh::lean_del_object(v___x_2702_);
                    v_force_2905_ = leanh::lean_ctor_get_uint8(v_f_2710_, 0 as u32);
                    leanh::lean_dec_ref_known(v_f_2710_, 0);
                    v___x_2906_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2704_);
                    if v___x_2906_ == 0 {
                        v___y_2757_ = v___x_2906_;
                        state = 8;
                        continue;
                    } else {
                        if v_force_2905_ == 0 {
                            v___y_2757_ = v___x_2906_;
                            state = 8;
                            continue;
                        } else {
                            state = 4;
                            continue;
                        }
                    }
                }
                3 => {
                    leanh::lean_del_object(v___x_2702_);
                    v_a_2907_ = leanh::lean_ctor_get(v_f_2710_, 0);
                    v_isSharedCheck_2970_ = (!leanh::lean_is_exclusive(v_f_2710_)) as u8;
                    if v_isSharedCheck_2970_ == 0 {
                        v___x_2909_ = v_f_2710_;
                        v_isShared_2910_ = v_isSharedCheck_2970_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2907_);
                        leanh::lean_dec(v_f_2710_);
                        v___x_2909_ = leanh::lean_box(0);
                        v_isShared_2910_ = v_isSharedCheck_2970_;
                        state = 23;
                        continue;
                    }
                }
                4 => {
                    leanh::lean_del_object(v___x_2702_);
                    v_indent_2971_ = leanh::lean_ctor_get(v_f_2710_, 0);
                    leanh::lean_inc(v_indent_2971_);
                    v_f_2972_ = leanh::lean_ctor_get(v_f_2710_, 1);
                    leanh::lean_inc(v_f_2972_);
                    leanh::lean_dec_ref_known(v_f_2710_, 2);
                    v___x_2973_ = lean_int_add(v_indent_2711_, v_indent_2971_);
                    leanh::lean_dec(v_indent_2971_);
                    leanh::lean_dec(v_indent_2711_);
                    if v_isShared_2715_ == 0 {
                        leanh::lean_ctor_set(v___x_2714_, 1, v___x_2973_);
                        leanh::lean_ctor_set(v___x_2714_, 0, v_f_2972_);
                        v___x_2975_ = v___x_2714_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2981_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_f_2972_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2973_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_activeTags_2712_);
                        v___x_2975_ = v_reuseFailAlloc_2981_;
                        state = 31;
                        continue;
                    }
                }
                5 => {
                    v_a_2982_ = leanh::lean_ctor_get(v_f_2710_, 0);
                    leanh::lean_inc(v_a_2982_);
                    v_a_2983_ = leanh::lean_ctor_get(v_f_2710_, 1);
                    leanh::lean_inc(v_a_2983_);
                    leanh::lean_dec_ref_known(v_f_2710_, 2);
                    v___x_2984_ = leanh::lean_unsigned_to_nat(0);
                    leanh::lean_inc(v_indent_2711_);
                    if v_isShared_2715_ == 0 {
                        leanh::lean_ctor_set(v___x_2714_, 2, v___x_2984_);
                        leanh::lean_ctor_set(v___x_2714_, 0, v_a_2982_);
                        v___x_2986_ = v___x_2714_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_2996_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2982_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_indent_2711_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 2, v___x_2984_);
                        v___x_2986_ = v_reuseFailAlloc_2996_;
                        state = 33;
                        continue;
                    }
                }
                6 => {
                    leanh::lean_del_object(v___x_2702_);
                    v_a_2997_ = leanh::lean_ctor_get(v_f_2710_, 0);
                    leanh::lean_inc(v_a_2997_);
                    v_behavior_2998_ = leanh::lean_ctor_get_uint8(
                        v_f_2710_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    leanh::lean_dec_ref_known(v_f_2710_, 1);
                    v___x_2999_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2704_);
                    if v___x_2999_ == 0 {
                        if v_isShared_2715_ == 0 {
                            leanh::lean_ctor_set(v___x_2714_, 0, v_a_2997_);
                            v___x_3001_ = v___x_2714_;
                            state = 36;
                            continue;
                        } else {
                            v_reuseFailAlloc_3011_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_2997_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_indent_2711_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3011_,
                                2,
                                v_activeTags_2712_,
                            );
                            v___x_3001_ = v_reuseFailAlloc_3011_;
                            state = 36;
                            continue;
                        }
                    } else {
                        if v_isShared_2715_ == 0 {
                            leanh::lean_ctor_set(v___x_2714_, 0, v_a_2997_);
                            v___x_3013_ = v___x_2714_;
                            state = 38;
                            continue;
                        } else {
                            v_reuseFailAlloc_3019_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_2997_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_indent_2711_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3019_,
                                2,
                                v_activeTags_2712_,
                            );
                            v___x_3013_ = v_reuseFailAlloc_3019_;
                            state = 38;
                            continue;
                        }
                    }
                }
                _ => {
                    v_a_3020_ = leanh::lean_ctor_get(v_f_2710_, 0);
                    leanh::lean_inc(v_a_3020_);
                    v_a_3021_ = leanh::lean_ctor_get(v_f_2710_, 1);
                    leanh::lean_inc(v_a_3021_);
                    leanh::lean_dec_ref_known(v_f_2710_, 2);
                    v_out_3022_ = leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_3023_ = leanh::lean_ctor_get(v___y_2692_, 1);
                    v_column_3024_ = leanh::lean_ctor_get(v___y_2692_, 2);
                    v_isSharedCheck_3047_ = (!leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_3047_ == 0 {
                        v___x_3026_ = v___y_2692_;
                        v_isShared_3027_ = v_isSharedCheck_3047_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_inc(v_column_3024_);
                        leanh::lean_inc(v_tagStack_3023_);
                        leanh::lean_inc(v_out_3022_);
                        leanh::lean_dec(v___y_2692_);
                        v___x_3026_ = leanh::lean_box(0);
                        v_isShared_3027_ = v_isSharedCheck_3047_;
                        state = 40;
                        continue;
                    }
                }
            },
            4 => {
                v_out_2717_ = leanh::lean_ctor_get(v___y_2692_, 0);
                v_tagStack_2718_ = leanh::lean_ctor_get(v___y_2692_, 1);
                v_column_2719_ = leanh::lean_ctor_get(v___y_2692_, 2);
                v_isSharedCheck_2755_ = (!leanh::lean_is_exclusive(v___y_2692_)) as u8;
                if v_isSharedCheck_2755_ == 0 {
                    v___x_2721_ = v___y_2692_;
                    v_isShared_2722_ = v_isSharedCheck_2755_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_column_2719_);
                    leanh::lean_inc(v_tagStack_2718_);
                    leanh::lean_inc(v_out_2717_);
                    leanh::lean_dec(v___y_2692_);
                    v___x_2721_ = leanh::lean_box(0);
                    v_isShared_2722_ = v_isSharedCheck_2755_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc(v_column_2719_);
                v___x_2723_ = lean_nat_to_int(v_column_2719_);
                v___x_2724_ = lean_int_dec_lt(v___x_2723_, v_indent_2711_);
                if v___x_2724_ == 0 {
                    leanh::lean_dec(v___x_2723_);
                    leanh::lean_dec(v_column_2719_);
                    v___x_2725_ = l_Int_toNat(v_indent_2711_);
                    leanh::lean_dec(v_indent_2711_);
                    v___x_2726_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                    leanh::lean_inc(v___x_2725_);
                    v___x_2727_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2725_, v___x_2726_);
                    v___x_2728_ =
                        l_Lean_Widget_TaggedText_appendText___redArg(v___x_2727_, v_out_2717_);
                    v___x_2729_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                    leanh::lean_inc(v_activeTags_2712_);
                    leanh::lean_inc(v_tagStack_2718_);
                    v___x_2730_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                        leanh::lean_box(0),
                        v_tagStack_2718_,
                        v_tagStack_2718_,
                        v_activeTags_2712_,
                        v___x_2729_,
                    );
                    v___x_2731_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2718_);
                    leanh::lean_dec(v_tagStack_2718_);
                    v_out_x27_2732_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2728_, v___x_2730_);
                    if v_isShared_2722_ == 0 {
                        leanh::lean_ctor_set(v___x_2721_, 2, v___x_2725_);
                        leanh::lean_ctor_set(v___x_2721_, 1, v___x_2731_);
                        leanh::lean_ctor_set(v___x_2721_, 0, v_out_x27_2732_);
                        v___x_2734_ = v___x_2721_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2737_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_out_x27_2732_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 1, v___x_2731_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 2, v___x_2725_);
                        v___x_2734_ = v_reuseFailAlloc_2737_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_2738_ = l_Lean_Widget_instInhabitedTaggedText_default___closed__0;
                    v___x_2739_ = 32;
                    v___x_2740_ = lean_int_sub(v_indent_2711_, v___x_2723_);
                    leanh::lean_dec(v___x_2723_);
                    leanh::lean_dec(v_indent_2711_);
                    v___x_2741_ = l_Int_toNat(v___x_2740_);
                    leanh::lean_dec(v___x_2740_);
                    v___x_2742_ = lean_string_pushn(v___x_2738_, v___x_2739_, v___x_2741_);
                    leanh::lean_inc_ref(v___x_2742_);
                    v___x_2743_ =
                        l_Lean_Widget_TaggedText_appendText___redArg(v___x_2742_, v_out_2717_);
                    v___x_2744_ = lean_string_length(v___x_2742_);
                    leanh::lean_dec_ref(v___x_2742_);
                    v___x_2745_ = lean_nat_add(v_column_2719_, v___x_2744_);
                    leanh::lean_dec(v_column_2719_);
                    v___x_2746_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                    leanh::lean_inc(v_activeTags_2712_);
                    leanh::lean_inc(v_tagStack_2718_);
                    v___x_2747_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                        leanh::lean_box(0),
                        v_tagStack_2718_,
                        v_tagStack_2718_,
                        v_activeTags_2712_,
                        v___x_2746_,
                    );
                    v___x_2748_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2718_);
                    leanh::lean_dec(v_tagStack_2718_);
                    v_out_x27_2749_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2743_, v___x_2747_);
                    if v_isShared_2722_ == 0 {
                        leanh::lean_ctor_set(v___x_2721_, 2, v___x_2745_);
                        leanh::lean_ctor_set(v___x_2721_, 1, v___x_2748_);
                        leanh::lean_ctor_set(v___x_2721_, 0, v_out_x27_2749_);
                        v___x_2751_ = v___x_2721_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2754_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_out_x27_2749_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 1, v___x_2748_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 2, v___x_2745_);
                        v___x_2751_ = v_reuseFailAlloc_2754_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2735_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_tail_2706_);
                v_x_2691_ = v___x_2735_;
                v___y_2692_ = v___x_2734_;
                state = 0;
                continue;
            }
            7 => {
                v___x_2752_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_tail_2706_);
                v_x_2691_ = v___x_2752_;
                v___y_2692_ = v___x_2751_;
                state = 0;
                continue;
            }
            8 => {
                if v___y_2757_ == 0 {
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_indent_2711_);
                    v_out_2758_ = leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_2759_ = leanh::lean_ctor_get(v___y_2692_, 1);
                    v_column_2760_ = leanh::lean_ctor_get(v___y_2692_, 2);
                    v_isSharedCheck_2773_ = (!leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_2773_ == 0 {
                        v___x_2762_ = v___y_2692_;
                        v_isShared_2763_ = v_isSharedCheck_2773_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_column_2760_);
                        leanh::lean_inc(v_tagStack_2759_);
                        leanh::lean_inc(v_out_2758_);
                        leanh::lean_dec(v___y_2692_);
                        v___x_2762_ = leanh::lean_box(0);
                        v_isShared_2763_ = v_isSharedCheck_2773_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2764_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                leanh::lean_inc(v_activeTags_2712_);
                leanh::lean_inc(v_tagStack_2759_);
                v___x_2765_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    leanh::lean_box(0),
                    v_tagStack_2759_,
                    v_tagStack_2759_,
                    v_activeTags_2712_,
                    v___x_2764_,
                );
                v___x_2766_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2759_);
                leanh::lean_dec(v_tagStack_2759_);
                v_out_x27_2767_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_2758_, v___x_2765_);
                if v_isShared_2763_ == 0 {
                    leanh::lean_ctor_set(v___x_2762_, 1, v___x_2766_);
                    leanh::lean_ctor_set(v___x_2762_, 0, v_out_x27_2767_);
                    v___x_2769_ = v___x_2762_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2772_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_out_x27_2767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 1, v___x_2766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_column_2760_);
                    v___x_2769_ = v_reuseFailAlloc_2772_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2770_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_tail_2706_);
                v_x_2691_ = v___x_2770_;
                v___y_2692_ = v___x_2769_;
                state = 0;
                continue;
            }
            11 => {
                v___x_2780_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                leanh::lean_inc(v_activeTags_2712_);
                leanh::lean_inc(v_tagStack_2775_);
                v___x_2781_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    leanh::lean_box(0),
                    v_tagStack_2775_,
                    v_tagStack_2775_,
                    v_activeTags_2712_,
                    v___x_2780_,
                );
                v___x_2782_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2775_);
                leanh::lean_dec(v_tagStack_2775_);
                v_out_x27_2783_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_2774_, v___x_2781_);
                if v_isShared_2779_ == 0 {
                    leanh::lean_ctor_set(v___x_2778_, 1, v___x_2782_);
                    leanh::lean_ctor_set(v___x_2778_, 0, v_out_x27_2783_);
                    v___x_2785_ = v___x_2778_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2788_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_out_x27_2783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_column_2776_);
                    v___x_2785_ = v_reuseFailAlloc_2788_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2786_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_tail_2706_);
                v_x_2691_ = v___x_2786_;
                v___y_2692_ = v___x_2785_;
                state = 0;
                continue;
            }
            13 => {
                v___x_2796_ = l_Int_toNat(v_indent_2711_);
                leanh::lean_dec(v_indent_2711_);
                v___x_2797_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                leanh::lean_inc(v___x_2796_);
                v___x_2798_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2796_, v___x_2797_);
                v___x_2799_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2798_, v_out_2791_);
                v___x_2800_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                leanh::lean_inc(v_activeTags_2712_);
                leanh::lean_inc(v_tagStack_2792_);
                v___x_2801_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    leanh::lean_box(0),
                    v_tagStack_2792_,
                    v_tagStack_2792_,
                    v_activeTags_2712_,
                    v___x_2800_,
                );
                v___x_2802_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2792_);
                leanh::lean_dec(v_tagStack_2792_);
                v_out_x27_2803_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2799_, v___x_2801_);
                if v_isShared_2795_ == 0 {
                    leanh::lean_ctor_set(v___x_2794_, 2, v___x_2796_);
                    leanh::lean_ctor_set(v___x_2794_, 1, v___x_2802_);
                    leanh::lean_ctor_set(v___x_2794_, 0, v_out_x27_2803_);
                    v___x_2805_ = v___x_2794_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_out_x27_2803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 1, v___x_2802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 2, v___x_2796_);
                    v___x_2805_ = v_reuseFailAlloc_2808_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2806_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_tail_2706_);
                v_x_2691_ = v___x_2806_;
                v___y_2692_ = v___x_2805_;
                state = 0;
                continue;
            }
            15 => {
                v___x_2817_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0;
                v___x_2818_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2817_, v_out_2811_);
                v___x_2819_ = leanh::lean_unsigned_to_nat(1);
                v___x_2820_ = lean_nat_add(v_column_2813_, v___x_2819_);
                leanh::lean_dec(v_column_2813_);
                v___x_2821_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                leanh::lean_inc(v_activeTags_2712_);
                leanh::lean_inc(v_tagStack_2812_);
                v___x_2822_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    leanh::lean_box(0),
                    v_tagStack_2812_,
                    v_tagStack_2812_,
                    v_activeTags_2712_,
                    v___x_2821_,
                );
                v___x_2823_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2812_);
                leanh::lean_dec(v_tagStack_2812_);
                v_out_x27_2824_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2818_, v___x_2822_);
                if v_isShared_2816_ == 0 {
                    leanh::lean_ctor_set(v___x_2815_, 2, v___x_2820_);
                    leanh::lean_ctor_set(v___x_2815_, 1, v___x_2823_);
                    leanh::lean_ctor_set(v___x_2815_, 0, v_out_x27_2824_);
                    v___x_2826_ = v___x_2815_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2829_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_out_x27_2824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 1, v___x_2823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 2, v___x_2820_);
                    v___x_2826_ = v_reuseFailAlloc_2829_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2827_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_tail_2706_);
                v_x_2691_ = v___x_2827_;
                v___y_2692_ = v___x_2826_;
                state = 0;
                continue;
            }
            17 => {
                v___x_2838_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                leanh::lean_inc(v___x_2831_);
                v___x_2839_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2831_, v___x_2838_);
                v___x_2840_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2839_, v_out_2833_);
                v___x_2841_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                leanh::lean_inc(v_activeTags_2712_);
                leanh::lean_inc(v_tagStack_2834_);
                v___x_2842_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    leanh::lean_box(0),
                    v_tagStack_2834_,
                    v_tagStack_2834_,
                    v_activeTags_2712_,
                    v___x_2841_,
                );
                v___x_2843_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2834_);
                leanh::lean_dec(v_tagStack_2834_);
                v_out_x27_2844_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2840_, v___x_2842_);
                if v_isShared_2837_ == 0 {
                    leanh::lean_ctor_set(v___x_2836_, 2, v___x_2831_);
                    leanh::lean_ctor_set(v___x_2836_, 1, v___x_2843_);
                    leanh::lean_ctor_set(v___x_2836_, 0, v_out_x27_2844_);
                    v___x_2846_ = v___x_2836_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_out_x27_2844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2843_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 2, v___x_2831_);
                    v___x_2846_ = v_reuseFailAlloc_2851_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2847_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_2705_, v_tail_2706_, v_tail_2700_, v_w_2690_, v___x_2846_);
                v_fst_2848_ = leanh::lean_ctor_get(v___x_2847_, 0);
                leanh::lean_inc(v_fst_2848_);
                v_snd_2849_ = leanh::lean_ctor_get(v___x_2847_, 1);
                leanh::lean_inc(v_snd_2849_);
                leanh::lean_dec_ref(v___x_2847_);
                v_x_2691_ = v_fst_2848_;
                v___y_2692_ = v_snd_2849_;
                state = 0;
                continue;
            }
            19 => {
                v___x_2868_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                leanh::lean_inc(v___x_2831_);
                v___x_2869_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2831_, v___x_2868_);
                v___x_2870_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2869_, v_out_2863_);
                v___x_2871_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                leanh::lean_inc(v_activeTags_2712_);
                leanh::lean_inc(v_tagStack_2864_);
                v___x_2872_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    leanh::lean_box(0),
                    v_tagStack_2864_,
                    v_tagStack_2864_,
                    v_activeTags_2712_,
                    v___x_2871_,
                );
                v___x_2873_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2864_);
                leanh::lean_dec(v_tagStack_2864_);
                v_out_x27_2874_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2870_, v___x_2872_);
                if v_isShared_2867_ == 0 {
                    leanh::lean_ctor_set(v___x_2866_, 2, v___x_2831_);
                    leanh::lean_ctor_set(v___x_2866_, 1, v___x_2873_);
                    leanh::lean_ctor_set(v___x_2866_, 0, v_out_x27_2874_);
                    v___x_2876_ = v___x_2866_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2881_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_out_x27_2874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 1, v___x_2873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 2, v___x_2831_);
                    v___x_2876_ = v_reuseFailAlloc_2881_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_2877_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_2705_, v_tail_2706_, v_tail_2700_, v_w_2690_, v___x_2876_);
                v_fst_2878_ = leanh::lean_ctor_get(v___x_2877_, 0);
                leanh::lean_inc(v_fst_2878_);
                v_snd_2879_ = leanh::lean_ctor_get(v___x_2877_, 1);
                leanh::lean_inc(v_snd_2879_);
                leanh::lean_dec_ref(v___x_2877_);
                v_x_2691_ = v_fst_2878_;
                v___y_2692_ = v_snd_2879_;
                state = 0;
                continue;
            }
            21 => {
                v___x_2890_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2854_, v_out_2884_);
                v___x_2891_ = leanh::lean_unsigned_to_nat(1);
                v___x_2892_ = lean_nat_add(v_column_2886_, v___x_2891_);
                leanh::lean_dec(v_column_2886_);
                v___x_2893_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                leanh::lean_inc(v_activeTags_2712_);
                leanh::lean_inc(v_tagStack_2885_);
                v___x_2894_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    leanh::lean_box(0),
                    v_tagStack_2885_,
                    v_tagStack_2885_,
                    v_activeTags_2712_,
                    v___x_2893_,
                );
                v___x_2895_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2885_);
                leanh::lean_dec(v_tagStack_2885_);
                v_out_x27_2896_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2890_, v___x_2894_);
                if v_isShared_2889_ == 0 {
                    leanh::lean_ctor_set(v___x_2888_, 2, v___x_2892_);
                    leanh::lean_ctor_set(v___x_2888_, 1, v___x_2895_);
                    leanh::lean_ctor_set(v___x_2888_, 0, v_out_x27_2896_);
                    v___x_2898_ = v___x_2888_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2900_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_out_x27_2896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 2, v___x_2892_);
                    v___x_2898_ = v_reuseFailAlloc_2900_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v_x_2691_ = v_fst_2858_;
                v___y_2692_ = v___x_2898_;
                state = 0;
                continue;
            }
            23 => {
                v___x_2911_ = 10;
                leanh::lean_inc_ref(v_a_2907_);
                v_p_2912_ = lean_string_posof(v_a_2907_, v___x_2911_);
                v___x_2913_ = lean_string_utf8_byte_size(v_a_2907_);
                v___x_2914_ = lean_nat_dec_eq(v_p_2912_, v___x_2913_);
                if v___x_2914_ == 0 {
                    v_out_2915_ = leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_2916_ = leanh::lean_ctor_get(v___y_2692_, 1);
                    v_isSharedCheck_2949_ = (!leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_2949_ == 0 {
                        v_unused_2950_ = leanh::lean_ctor_get(v___y_2692_, 2);
                        leanh::lean_dec(v_unused_2950_);
                        v___x_2918_ = v___y_2692_;
                        v_isShared_2919_ = v_isSharedCheck_2949_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_tagStack_2916_);
                        leanh::lean_inc(v_out_2915_);
                        leanh::lean_dec(v___y_2692_);
                        v___x_2918_ = leanh::lean_box(0);
                        v_isShared_2919_ = v_isSharedCheck_2949_;
                        state = 24;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_p_2912_);
                    leanh::lean_del_object(v___x_2909_);
                    leanh::lean_del_object(v___x_2714_);
                    leanh::lean_dec(v_indent_2711_);
                    leanh::lean_del_object(v___x_2708_);
                    v_out_2951_ = leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_2952_ = leanh::lean_ctor_get(v___y_2692_, 1);
                    v_column_2953_ = leanh::lean_ctor_get(v___y_2692_, 2);
                    v_isSharedCheck_2969_ = (!leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_2969_ == 0 {
                        v___x_2955_ = v___y_2692_;
                        v_isShared_2956_ = v_isSharedCheck_2969_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_inc(v_column_2953_);
                        leanh::lean_inc(v_tagStack_2952_);
                        leanh::lean_inc(v_out_2951_);
                        leanh::lean_dec(v___y_2692_);
                        v___x_2955_ = leanh::lean_box(0);
                        v_isShared_2956_ = v_isSharedCheck_2969_;
                        state = 29;
                        continue;
                    }
                }
            }
            24 => {
                v___x_2920_ = leanh::lean_unsigned_to_nat(0);
                v___x_2921_ = lean_string_utf8_extract(v_a_2907_, v___x_2920_, v_p_2912_);
                v___x_2922_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2921_, v_out_2915_);
                v___x_2923_ = l_Int_toNat(v_indent_2711_);
                v___x_2924_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                leanh::lean_inc(v___x_2923_);
                v___x_2925_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2923_, v___x_2924_);
                v___x_2926_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2925_, v___x_2922_);
                if v_isShared_2919_ == 0 {
                    leanh::lean_ctor_set(v___x_2918_, 2, v___x_2923_);
                    leanh::lean_ctor_set(v___x_2918_, 0, v___x_2926_);
                    v___x_2928_ = v___x_2918_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2948_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_tagStack_2916_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 2, v___x_2923_);
                    v___x_2928_ = v_reuseFailAlloc_2948_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_2929_ = lean_string_utf8_next(v_a_2907_, v_p_2912_);
                leanh::lean_dec(v_p_2912_);
                v___x_2930_ = lean_string_utf8_extract(v_a_2907_, v___x_2929_, v___x_2913_);
                leanh::lean_dec(v___x_2929_);
                leanh::lean_dec_ref(v_a_2907_);
                if v_isShared_2910_ == 0 {
                    leanh::lean_ctor_set(v___x_2909_, 0, v___x_2930_);
                    v___x_2932_ = v___x_2909_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2930_);
                    v___x_2932_ = v_reuseFailAlloc_2947_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_2715_ == 0 {
                    leanh::lean_ctor_set(v___x_2714_, 0, v___x_2932_);
                    v___x_2934_ = v___x_2714_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2946_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_indent_2711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_activeTags_2712_);
                    v___x_2934_ = v_reuseFailAlloc_2946_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2709_ == 0 {
                    leanh::lean_ctor_set(v___x_2708_, 0, v___x_2934_);
                    v_is_2936_ = v___x_2708_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2945_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_tail_2706_);
                    v_is_2936_ = v_reuseFailAlloc_2945_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_2937_ = leanh::lean_box(1);
                v___x_2938_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_2704_, v___x_2937_);
                if v___x_2938_ == 0 {
                    leanh::lean_dec(v_fla_2704_);
                    v___x_2939_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_2705_, v_is_2936_, v_tail_2700_, v_w_2690_, v___x_2928_);
                    v_fst_2940_ = leanh::lean_ctor_get(v___x_2939_, 0);
                    leanh::lean_inc(v_fst_2940_);
                    v_snd_2941_ = leanh::lean_ctor_get(v___x_2939_, 1);
                    leanh::lean_inc(v_snd_2941_);
                    leanh::lean_dec_ref(v___x_2939_);
                    v_x_2691_ = v_fst_2940_;
                    v___y_2692_ = v_snd_2941_;
                    state = 0;
                    continue;
                } else {
                    v___x_2943_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_is_2936_);
                    v_x_2691_ = v___x_2943_;
                    v___y_2692_ = v___x_2928_;
                    state = 0;
                    continue;
                }
            }
            29 => {
                leanh::lean_inc_ref(v_a_2907_);
                v___x_2957_ = l_Lean_Widget_TaggedText_appendText___redArg(v_a_2907_, v_out_2951_);
                v___x_2958_ = lean_string_length(v_a_2907_);
                leanh::lean_dec_ref(v_a_2907_);
                v___x_2959_ = lean_nat_add(v_column_2953_, v___x_2958_);
                leanh::lean_dec(v_column_2953_);
                v___x_2960_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                leanh::lean_inc(v_activeTags_2712_);
                leanh::lean_inc(v_tagStack_2952_);
                v___x_2961_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    leanh::lean_box(0),
                    v_tagStack_2952_,
                    v_tagStack_2952_,
                    v_activeTags_2712_,
                    v___x_2960_,
                );
                v___x_2962_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2952_);
                leanh::lean_dec(v_tagStack_2952_);
                v_out_x27_2963_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2957_, v___x_2961_);
                if v_isShared_2956_ == 0 {
                    leanh::lean_ctor_set(v___x_2955_, 2, v___x_2959_);
                    leanh::lean_ctor_set(v___x_2955_, 1, v___x_2962_);
                    leanh::lean_ctor_set(v___x_2955_, 0, v_out_x27_2963_);
                    v___x_2965_ = v___x_2955_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2968_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_out_x27_2963_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2968_, 2, v___x_2959_);
                    v___x_2965_ = v_reuseFailAlloc_2968_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2966_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_tail_2706_);
                v_x_2691_ = v___x_2966_;
                v___y_2692_ = v___x_2965_;
                state = 0;
                continue;
            }
            31 => {
                if v_isShared_2709_ == 0 {
                    leanh::lean_ctor_set(v___x_2708_, 0, v___x_2975_);
                    v___x_2977_ = v___x_2708_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2980_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_tail_2706_);
                    v___x_2977_ = v_reuseFailAlloc_2980_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_2978_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v___x_2977_);
                v_x_2691_ = v___x_2978_;
                state = 0;
                continue;
            }
            33 => {
                v___x_2987_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2987_, 0, v_a_2983_);
                leanh::lean_ctor_set(v___x_2987_, 1, v_indent_2711_);
                leanh::lean_ctor_set(v___x_2987_, 2, v_activeTags_2712_);
                if v_isShared_2709_ == 0 {
                    leanh::lean_ctor_set(v___x_2708_, 0, v___x_2987_);
                    v___x_2989_ = v___x_2708_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2995_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_tail_2706_);
                    v___x_2989_ = v_reuseFailAlloc_2995_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_2703_ == 0 {
                    leanh::lean_ctor_set(v___x_2702_, 1, v___x_2989_);
                    leanh::lean_ctor_set(v___x_2702_, 0, v___x_2986_);
                    v___x_2991_ = v___x_2702_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2994_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2986_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___x_2989_);
                    v___x_2991_ = v_reuseFailAlloc_2994_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2992_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v___x_2991_);
                v_x_2691_ = v___x_2992_;
                state = 0;
                continue;
            }
            36 => {
                v___x_3002_ = leanh::lean_box(0);
                if v_isShared_2709_ == 0 {
                    leanh::lean_ctor_set(v___x_2708_, 1, v___x_3002_);
                    leanh::lean_ctor_set(v___x_2708_, 0, v___x_3001_);
                    v___x_3004_ = v___x_2708_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3010_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___x_3002_);
                    v___x_3004_ = v_reuseFailAlloc_3010_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_3005_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_tail_2706_);
                v___x_3006_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_behavior_2998_, v___x_3004_, v___x_3005_, v_w_2690_, v___y_2692_);
                v_fst_3007_ = leanh::lean_ctor_get(v___x_3006_, 0);
                leanh::lean_inc(v_fst_3007_);
                v_snd_3008_ = leanh::lean_ctor_get(v___x_3006_, 1);
                leanh::lean_inc(v_snd_3008_);
                leanh::lean_dec_ref(v___x_3006_);
                v_x_2691_ = v_fst_3007_;
                v___y_2692_ = v_snd_3008_;
                state = 0;
                continue;
            }
            38 => {
                if v_isShared_2709_ == 0 {
                    leanh::lean_ctor_set(v___x_2708_, 0, v___x_3013_);
                    v___x_3015_ = v___x_2708_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_tail_2706_);
                    v___x_3015_ = v_reuseFailAlloc_3018_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v___x_3016_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v___x_3015_);
                v_x_2691_ = v___x_3016_;
                state = 0;
                continue;
            }
            40 => {
                v___x_3028_ = l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0;
                leanh::lean_inc(v_column_3024_);
                v___x_3029_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3029_, 0, v_column_3024_);
                leanh::lean_ctor_set(v___x_3029_, 1, v_out_3022_);
                v___x_3030_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3030_, 0, v_a_3020_);
                leanh::lean_ctor_set(v___x_3030_, 1, v___x_3029_);
                if v_isShared_2709_ == 0 {
                    leanh::lean_ctor_set(v___x_2708_, 1, v_tagStack_3023_);
                    leanh::lean_ctor_set(v___x_2708_, 0, v___x_3030_);
                    v___x_3032_ = v___x_2708_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_tagStack_3023_);
                    v___x_3032_ = v_reuseFailAlloc_3046_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_3027_ == 0 {
                    leanh::lean_ctor_set(v___x_3026_, 1, v___x_3032_);
                    leanh::lean_ctor_set(v___x_3026_, 0, v___x_3028_);
                    v___x_3034_ = v___x_3026_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3045_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 2, v_column_3024_);
                    v___x_3034_ = v_reuseFailAlloc_3045_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v___x_3035_ = leanh::lean_unsigned_to_nat(1);
                v___x_3036_ = lean_nat_add(v_activeTags_2712_, v___x_3035_);
                leanh::lean_dec(v_activeTags_2712_);
                if v_isShared_2715_ == 0 {
                    leanh::lean_ctor_set(v___x_2714_, 2, v___x_3036_);
                    leanh::lean_ctor_set(v___x_2714_, 0, v_a_3021_);
                    v___x_3038_ = v___x_2714_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3044_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3021_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_indent_2711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 2, v___x_3036_);
                    v___x_3038_ = v_reuseFailAlloc_3044_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_2703_ == 0 {
                    leanh::lean_ctor_set(v___x_2702_, 1, v_tail_2706_);
                    leanh::lean_ctor_set(v___x_2702_, 0, v___x_3038_);
                    v___x_3040_ = v___x_2702_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3043_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_tail_2706_);
                    v___x_3040_ = v_reuseFailAlloc_3043_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_3041_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v___x_3040_);
                v_x_2691_ = v___x_3041_;
                v___y_2692_ = v___x_3034_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___boxed(
    mut v_w_3053_: *mut leanh::LeanObject,
    mut v_x_3054_: *mut leanh::LeanObject,
    mut v___y_3055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_3053_, v_x_3054_, v___y_3055_);
    leanh::lean_dec(v_w_3053_);
    return v_res_3056_;
}
pub unsafe fn l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(
    mut v_f_3057_: *mut leanh::LeanObject,
    mut v_w_3058_: *mut leanh::LeanObject,
    mut v_indent_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: u8 = 0;
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3061_ = leanh::lean_box(1);
    v___x_3062_ = 0;
    v___x_3063_ = lean_nat_to_int(v_indent_3059_);
    v___x_3064_ = leanh::lean_unsigned_to_nat(0);
    v___x_3065_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3065_, 0, v_f_3057_);
    leanh::lean_ctor_set(v___x_3065_, 1, v___x_3063_);
    leanh::lean_ctor_set(v___x_3065_, 2, v___x_3064_);
    v___x_3066_ = leanh::lean_box(0);
    v___x_3067_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3067_, 0, v___x_3065_);
    leanh::lean_ctor_set(v___x_3067_, 1, v___x_3066_);
    v___x_3068_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_3068_, 0, v___x_3061_);
    leanh::lean_ctor_set(v___x_3068_, 1, v___x_3067_);
    leanh::lean_ctor_set_uint8(
        v___x_3068_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_3062_,
    );
    v___x_3069_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3069_, 0, v___x_3068_);
    leanh::lean_ctor_set(v___x_3069_, 1, v___x_3066_);
    v___x_3070_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_3058_, v___x_3069_, v___y_3060_);
    return v___x_3070_;
}
pub unsafe fn l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0___boxed(
    mut v_f_3071_: *mut leanh::LeanObject,
    mut v_w_3072_: *mut leanh::LeanObject,
    mut v_indent_3073_: *mut leanh::LeanObject,
    mut v___y_3074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(
        v_f_3071_,
        v_w_3072_,
        v_indent_3073_,
        v___y_3074_,
    );
    leanh::lean_dec(v_w_3072_);
    return v_res_3075_;
}
pub unsafe fn l_Lean_Widget_TaggedText_prettyTagged(
    mut v_f_3076_: *mut leanh::LeanObject,
    mut v_indent_3077_: *mut leanh::LeanObject,
    mut v_w_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3079_ = l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1;
    v___x_3080_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(
        v_f_3076_,
        v_w_3078_,
        v_indent_3077_,
        v___x_3079_,
    );
    v_snd_3081_ = leanh::lean_ctor_get(v___x_3080_, 1);
    leanh::lean_inc(v_snd_3081_);
    leanh::lean_dec_ref(v___x_3080_);
    v_out_3082_ = leanh::lean_ctor_get(v_snd_3081_, 0);
    leanh::lean_inc_ref(v_out_3082_);
    leanh::lean_dec(v_snd_3081_);
    return v_out_3082_;
}
pub unsafe fn l_Lean_Widget_TaggedText_prettyTagged___boxed(
    mut v_f_3083_: *mut leanh::LeanObject,
    mut v_indent_3084_: *mut leanh::LeanObject,
    mut v_w_3085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3086_ = l_Lean_Widget_TaggedText_prettyTagged(v_f_3083_, v_indent_3084_, v_w_3085_);
    leanh::lean_dec(v_w_3085_);
    return v_res_3086_;
}
pub unsafe fn l_Nat_cast___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__0(
    mut v_a_3087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3088_ = lean_nat_to_int(v_a_3087_);
    return v___x_3088_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(
    mut v_acc_3089_: *mut leanh::LeanObject,
    mut v_a_3090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3091_ = lean_array_get_size(v_a_3090_);
                v___x_3092_ = leanh::lean_unsigned_to_nat(0);
                v___x_3093_ = lean_nat_dec_eq(v___x_3091_, v___x_3092_);
                if v___x_3093_ == 0 {
                    v___x_3094_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instInhabitedTaggedText___closed__0_once
                        ),
                        _init_l_Lean_Widget_instInhabitedTaggedText___closed__0,
                    );
                    v___x_3095_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3096_ = lean_nat_sub(v___x_3091_, v___x_3095_);
                    v___x_3097_ = lean_array_get_borrowed(v___x_3094_, v_a_3090_, v___x_3096_);
                    match leanh::lean_obj_tag(v___x_3097_) {
                        0 => {
                            leanh::lean_dec(v___x_3096_);
                            v_a_3098_ = leanh::lean_ctor_get(v___x_3097_, 0);
                            v___x_3099_ = lean_string_append(v_acc_3089_, v_a_3098_);
                            v___x_3100_ = lean_array_pop(v_a_3090_);
                            v_acc_3089_ = v___x_3099_;
                            v_a_3090_ = v___x_3100_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_dec(v___x_3096_);
                            v_a_3102_ = leanh::lean_ctor_get(v___x_3097_, 0);
                            leanh::lean_inc_ref(v_a_3102_);
                            v___x_3103_ = lean_array_pop(v_a_3090_);
                            v___x_3104_ = l_Array_reverse___redArg(v_a_3102_);
                            v___x_3105_ = l_Array_append___redArg(v___x_3103_, v___x_3104_);
                            leanh::lean_dec_ref(v___x_3104_);
                            v_a_3090_ = v___x_3105_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v_a_3107_ = leanh::lean_ctor_get(v___x_3097_, 1);
                            leanh::lean_inc_ref(v_a_3107_);
                            v___x_3108_ = lean_array_set(v_a_3090_, v___x_3096_, v_a_3107_);
                            leanh::lean_dec(v___x_3096_);
                            v_a_3090_ = v___x_3108_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_3090_);
                    return v_acc_3089_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go(
    mut v_00_u03b1_3110_: *mut leanh::LeanObject,
    mut v_acc_3111_: *mut leanh::LeanObject,
    mut v_a_3112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3113_ =
        l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(
            v_acc_3111_,
            v_a_3112_,
        );
    return v___x_3113_;
}
pub unsafe fn l_Lean_Widget_TaggedText_stripTags___redArg(
    mut v_tt_3114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3115_ = l_Lean_Widget_instInhabitedTaggedText_default___closed__0;
    v___x_3116_ = leanh::lean_unsigned_to_nat(1);
    v___x_3117_ = lean_mk_empty_array_with_capacity(v___x_3116_);
    v___x_3118_ = lean_array_push(v___x_3117_, v_tt_3114_);
    v___x_3119_ =
        l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(
            v___x_3115_,
            v___x_3118_,
        );
    return v___x_3119_;
}
pub unsafe fn l_Lean_Widget_TaggedText_stripTags(
    mut v_00_u03b1_3120_: *mut leanh::LeanObject,
    mut v_tt_3121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3122_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_3121_);
    return v___x_3122_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_TaggedText(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Rpc_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_GetLit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1 = _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1();
    leanh::lean_mark_persistent(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_TaggedText(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_TaggedText(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Rpc_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_GetLit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_TaggedText(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_TaggedText(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Widget_TaggedText(builtin);
}