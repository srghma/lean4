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
static mut l_Lean_Widget_instInhabitedTaggedText_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instInhabitedTaggedText_default___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instInhabitedTaggedText_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instInhabitedTaggedText_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Widget_instInhabitedTaggedText___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Widget_instInhabitedTaggedText___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4_value:
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
    m_data: [116, 97, 103, 0],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_map as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__14_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_pure as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_bind as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32_value:
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
    m_fun: l_Lean_instFromJsonJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instInhabitedTaggedText_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_TaggedText_instInhabitedTaggedState_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instInhabitedTaggedState: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_get as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7_value: crate::leanh::LeanClosureObject<7> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 245 }, m_fun: l_StateT_bind as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 7, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0]};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Widget_TaggedText_ctorIdx___redArg(
    mut v_x_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1562_) {
        0 => {
            let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1563_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1563_;
        }
        1 => {
            let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1564_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1564_;
        }
        _ => {
            let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1565_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1565_;
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorIdx___redArg___boxed(
    mut v_x_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1567_ = l_Lean_Widget_TaggedText_ctorIdx___redArg(v_x_1566_);
    crate::leanh::lean_dec_ref(v_x_1566_);
    return v_res_1567_;
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorIdx(
    mut v_00_u03b1_1568_: *mut crate::leanh::LeanObject,
    mut v_x_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1570_ = l_Lean_Widget_TaggedText_ctorIdx___redArg(v_x_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorIdx___boxed(
    mut v_00_u03b1_1571_: *mut crate::leanh::LeanObject,
    mut v_x_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1573_ = l_Lean_Widget_TaggedText_ctorIdx(v_00_u03b1_1571_, v_x_1572_);
    crate::leanh::lean_dec_ref(v_x_1572_);
    return v_res_1573_;
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorElim___redArg(
    mut v_t_1574_: *mut crate::leanh::LeanObject,
    mut v_k_1575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1574_) == 2 {
        let mut v_a_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1576_ = crate::leanh::lean_ctor_get(v_t_1574_, 0);
        crate::leanh::lean_inc(v_a_1576_);
        v_a_1577_ = crate::leanh::lean_ctor_get(v_t_1574_, 1);
        crate::leanh::lean_inc_ref(v_a_1577_);
        crate::leanh::lean_dec_ref_known(v_t_1574_, 2);
        v___x_1578_ = crate::leanh::lean_apply_2(v_k_1575_, v_a_1576_, v_a_1577_);
        return v___x_1578_;
    } else {
        let mut v_a_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1579_ = crate::leanh::lean_ctor_get(v_t_1574_, 0);
        crate::leanh::lean_inc_ref(v_a_1579_);
        crate::leanh::lean_dec_ref(v_t_1574_);
        v___x_1580_ = crate::leanh::lean_apply_1(v_k_1575_, v_a_1579_);
        return v___x_1580_;
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorElim(
    mut v_00_u03b1_1581_: *mut crate::leanh::LeanObject,
    mut v_motive__1_1582_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1583_: *mut crate::leanh::LeanObject,
    mut v_t_1584_: *mut crate::leanh::LeanObject,
    mut v_h_1585_: *mut crate::leanh::LeanObject,
    mut v_k_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1584_, v_k_1586_);
    return v___x_1587_;
}
pub unsafe fn l_Lean_Widget_TaggedText_ctorElim___boxed(
    mut v_00_u03b1_1588_: *mut crate::leanh::LeanObject,
    mut v_motive__1_1589_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1590_: *mut crate::leanh::LeanObject,
    mut v_t_1591_: *mut crate::leanh::LeanObject,
    mut v_h_1592_: *mut crate::leanh::LeanObject,
    mut v_k_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Lean_Widget_TaggedText_ctorElim(
        v_00_u03b1_1588_,
        v_motive__1_1589_,
        v_ctorIdx_1590_,
        v_t_1591_,
        v_h_1592_,
        v_k_1593_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1590_);
    return v_res_1594_;
}
pub unsafe fn l_Lean_Widget_TaggedText_text_elim___redArg(
    mut v_t_1595_: *mut crate::leanh::LeanObject,
    mut v_text_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1595_, v_text_1596_);
    return v___x_1597_;
}
pub unsafe fn l_Lean_Widget_TaggedText_text_elim(
    mut v_00_u03b1_1598_: *mut crate::leanh::LeanObject,
    mut v_motive__1_1599_: *mut crate::leanh::LeanObject,
    mut v_t_1600_: *mut crate::leanh::LeanObject,
    mut v_h_1601_: *mut crate::leanh::LeanObject,
    mut v_text_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1600_, v_text_1602_);
    return v___x_1603_;
}
pub unsafe fn l_Lean_Widget_TaggedText_append_elim___redArg(
    mut v_t_1604_: *mut crate::leanh::LeanObject,
    mut v_append_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1604_, v_append_1605_);
    return v___x_1606_;
}
pub unsafe fn l_Lean_Widget_TaggedText_append_elim(
    mut v_00_u03b1_1607_: *mut crate::leanh::LeanObject,
    mut v_motive__1_1608_: *mut crate::leanh::LeanObject,
    mut v_t_1609_: *mut crate::leanh::LeanObject,
    mut v_h_1610_: *mut crate::leanh::LeanObject,
    mut v_append_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1612_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1609_, v_append_1611_);
    return v___x_1612_;
}
pub unsafe fn l_Lean_Widget_TaggedText_tag_elim___redArg(
    mut v_t_1613_: *mut crate::leanh::LeanObject,
    mut v_tag_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1615_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1613_, v_tag_1614_);
    return v___x_1615_;
}
pub unsafe fn l_Lean_Widget_TaggedText_tag_elim(
    mut v_00_u03b1_1616_: *mut crate::leanh::LeanObject,
    mut v_motive__1_1617_: *mut crate::leanh::LeanObject,
    mut v_t_1618_: *mut crate::leanh::LeanObject,
    mut v_h_1619_: *mut crate::leanh::LeanObject,
    mut v_tag_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = l_Lean_Widget_TaggedText_ctorElim___redArg(v_t_1618_, v_tag_1620_);
    return v___x_1621_;
}
pub unsafe fn l_Lean_Widget_instInhabitedTaggedText_default(
    mut v_00_u03b1_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = l_Lean_Widget_instInhabitedTaggedText_default___closed__1;
    return v___x_1626_;
}
pub unsafe fn _init_l_Lean_Widget_instInhabitedTaggedText___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Lean_Widget_instInhabitedTaggedText_default(crate::leanh::lean_box(0));
    return v___x_1627_;
}
pub unsafe fn l_Lean_Widget_instInhabitedTaggedText(
    mut v_a_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0_once),
        _init_l_Lean_Widget_instInhabitedTaggedText___closed__0,
    );
    return v___x_1629_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed(
    mut v_inst_1630_: *mut crate::leanh::LeanObject,
    mut v_x_1631_: *mut crate::leanh::LeanObject,
    mut v_x_1632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1633_: u8 = 0;
    let mut v_r_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1633_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_1630_, v_x_1631_, v_x_1632_);
    v_r_1634_ = crate::leanh::lean_box((v_res_1633_) as usize);
    return v_r_1634_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText_beq___redArg(
    mut v_inst_1635_: *mut crate::leanh::LeanObject,
    mut v_x_1636_: *mut crate::leanh::LeanObject,
    mut v_x_1637_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: u8 = 0;
    let mut v_a_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: u8 = 0;
    let mut v_a_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1636_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_inst_1635_);
                    if crate::leanh::lean_obj_tag(v_x_1637_) == 0 {
                        v_a_1638_ = crate::leanh::lean_ctor_get(v_x_1636_, 0);
                        crate::leanh::lean_inc_ref(v_a_1638_);
                        crate::leanh::lean_dec_ref_known(v_x_1636_, 1);
                        v_a_1639_ = crate::leanh::lean_ctor_get(v_x_1637_, 0);
                        crate::leanh::lean_inc_ref(v_a_1639_);
                        crate::leanh::lean_dec_ref_known(v_x_1637_, 1);
                        v___x_1640_ = lean_string_dec_eq(v_a_1638_, v_a_1639_);
                        crate::leanh::lean_dec_ref(v_a_1639_);
                        crate::leanh::lean_dec_ref(v_a_1638_);
                        return v___x_1640_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_1636_, 1);
                        crate::leanh::lean_dec_ref(v_x_1637_);
                        v___x_1641_ = 0;
                        return v___x_1641_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_1637_) == 1 {
                        v_a_1642_ = crate::leanh::lean_ctor_get(v_x_1636_, 0);
                        crate::leanh::lean_inc_ref(v_a_1642_);
                        crate::leanh::lean_dec_ref_known(v_x_1636_, 1);
                        v_a_1643_ = crate::leanh::lean_ctor_get(v_x_1637_, 0);
                        crate::leanh::lean_inc_ref(v_a_1643_);
                        crate::leanh::lean_dec_ref_known(v_x_1637_, 1);
                        v___x_1644_ = lean_array_get_size(v_a_1642_);
                        v___x_1645_ = lean_array_get_size(v_a_1643_);
                        v___x_1646_ = lean_nat_dec_eq(v___x_1644_, v___x_1645_);
                        if v___x_1646_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_1643_);
                            crate::leanh::lean_dec_ref(v_a_1642_);
                            crate::leanh::lean_dec_ref(v_inst_1635_);
                            return v___x_1646_;
                        } else {
                            v___x_1647_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Widget_instBEqTaggedText_beq___redArg___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___x_1647_, 0, v_inst_1635_);
                            v___x_1648_ = l_Array_isEqvAux___redArg(
                                v_a_1642_,
                                v_a_1643_,
                                v___x_1647_,
                                v___x_1644_,
                            );
                            crate::leanh::lean_dec_ref(v_a_1643_);
                            crate::leanh::lean_dec_ref(v_a_1642_);
                            return v___x_1648_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_1636_, 1);
                        crate::leanh::lean_dec_ref(v_x_1637_);
                        crate::leanh::lean_dec_ref(v_inst_1635_);
                        v___x_1649_ = 0;
                        return v___x_1649_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_1637_) == 2 {
                        v_a_1650_ = crate::leanh::lean_ctor_get(v_x_1636_, 0);
                        crate::leanh::lean_inc(v_a_1650_);
                        v_a_1651_ = crate::leanh::lean_ctor_get(v_x_1636_, 1);
                        crate::leanh::lean_inc_ref(v_a_1651_);
                        crate::leanh::lean_dec_ref_known(v_x_1636_, 2);
                        v_a_1652_ = crate::leanh::lean_ctor_get(v_x_1637_, 0);
                        crate::leanh::lean_inc(v_a_1652_);
                        v_a_1653_ = crate::leanh::lean_ctor_get(v_x_1637_, 1);
                        crate::leanh::lean_inc_ref(v_a_1653_);
                        crate::leanh::lean_dec_ref_known(v_x_1637_, 2);
                        crate::leanh::lean_inc_ref(v_inst_1635_);
                        v___x_1654_ =
                            crate::leanh::lean_apply_2(v_inst_1635_, v_a_1650_, v_a_1652_);
                        v___x_1655_ = (crate::leanh::lean_unbox(v___x_1654_) as u8);
                        if v___x_1655_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_1653_);
                            crate::leanh::lean_dec_ref(v_a_1651_);
                            crate::leanh::lean_dec_ref(v_inst_1635_);
                            v___x_1656_ = (crate::leanh::lean_unbox(v___x_1654_) as u8);
                            return v___x_1656_;
                        } else {
                            v_x_1636_ = v_a_1651_;
                            v_x_1637_ = v_a_1653_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_1636_, 2);
                        crate::leanh::lean_dec_ref(v_x_1637_);
                        crate::leanh::lean_dec_ref(v_inst_1635_);
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
    mut v_00_u03b1_1659_: *mut crate::leanh::LeanObject,
    mut v_inst_1660_: *mut crate::leanh::LeanObject,
    mut v_x_1661_: *mut crate::leanh::LeanObject,
    mut v_x_1662_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1663_: u8 = 0;
    v___x_1663_ = l_Lean_Widget_instBEqTaggedText_beq___redArg(v_inst_1660_, v_x_1661_, v_x_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText_beq___boxed(
    mut v_00_u03b1_1664_: *mut crate::leanh::LeanObject,
    mut v_inst_1665_: *mut crate::leanh::LeanObject,
    mut v_x_1666_: *mut crate::leanh::LeanObject,
    mut v_x_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1668_: u8 = 0;
    let mut v_r_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ =
        l_Lean_Widget_instBEqTaggedText_beq(v_00_u03b1_1664_, v_inst_1665_, v_x_1666_, v_x_1667_);
    v_r_1669_ = crate::leanh::lean_box((v_res_1668_) as usize);
    return v_r_1669_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText___redArg(
    mut v_inst_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_instBEqTaggedText_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1671_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1671_, 1, v_inst_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Lean_Widget_instBEqTaggedText(
    mut v_00_u03b1_1672_: *mut crate::leanh::LeanObject,
    mut v_inst_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_instBEqTaggedText_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1674_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1674_, 1, v_inst_1673_);
    return v___x_1674_;
}
pub unsafe fn _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1682_ = lean_nat_to_int(v___x_1681_);
    return v___x_1682_;
}
pub unsafe fn _init_l_Lean_Widget_instReprTaggedText_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1684_ = lean_nat_to_int(v___x_1683_);
    return v___x_1684_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText_repr___redArg___boxed(
    mut v_inst_1697_: *mut crate::leanh::LeanObject,
    mut v_x_1698_: *mut crate::leanh::LeanObject,
    mut v_prec_1699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1700_ =
        l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_1697_, v_x_1698_, v_prec_1699_);
    crate::leanh::lean_dec(v_prec_1699_);
    return v_res_1700_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText_repr___redArg(
    mut v_inst_1701_: *mut crate::leanh::LeanObject,
    mut v_x_1702_: *mut crate::leanh::LeanObject,
    mut v_prec_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1707_: u8 = 0;
    let mut v___y_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1724_: u8 = 0;
    let mut v_a_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localinst_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: u8 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: u8 = 0;
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1702_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_inst_1701_);
                    v_a_1704_ = crate::leanh::lean_ctor_get(v_x_1702_, 0);
                    v_isSharedCheck_1724_ = (!crate::leanh::lean_is_exclusive(v_x_1702_)) as u8;
                    if v_isSharedCheck_1724_ == 0 {
                        v___x_1706_ = v_x_1702_;
                        v_isShared_1707_ = v_isSharedCheck_1724_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1704_);
                        crate::leanh::lean_dec(v_x_1702_);
                        v___x_1706_ = crate::leanh::lean_box(0);
                        v_isShared_1707_ = v_isSharedCheck_1724_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_1725_ = crate::leanh::lean_ctor_get(v_x_1702_, 0);
                    crate::leanh::lean_inc_ref(v_a_1725_);
                    crate::leanh::lean_dec_ref_known(v_x_1702_, 1);
                    v_localinst_1726_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Widget_instReprTaggedText_repr___redArg___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v_localinst_1726_, 0, v_inst_1701_);
                    v___x_1736_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1737_ = lean_nat_dec_le(v___x_1736_, v_prec_1703_);
                    if v___x_1737_ == 0 {
                        v___x_1738_ = crate::leanh::lean_obj_once(
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
                        v___x_1739_ = crate::leanh::lean_obj_once(
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
                    v_a_1740_ = crate::leanh::lean_ctor_get(v_x_1702_, 0);
                    v_a_1741_ = crate::leanh::lean_ctor_get(v_x_1702_, 1);
                    v_isSharedCheck_1764_ = (!crate::leanh::lean_is_exclusive(v_x_1702_)) as u8;
                    if v_isSharedCheck_1764_ == 0 {
                        v___x_1743_ = v_x_1702_;
                        v_isShared_1744_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1741_);
                        crate::leanh::lean_inc(v_a_1740_);
                        crate::leanh::lean_dec(v_x_1702_);
                        v___x_1743_ = crate::leanh::lean_box(0);
                        v_isShared_1744_ = v_isSharedCheck_1764_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1720_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1721_ = lean_nat_dec_le(v___x_1720_, v_prec_1703_);
                if v___x_1721_ == 0 {
                    v___x_1722_ = crate::leanh::lean_obj_once(
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
                    v___x_1723_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_ctor_set_tag(v___x_1706_, 3);
                    crate::leanh::lean_ctor_set(v___x_1706_, 0, v___x_1711_);
                    v___x_1713_ = v___x_1706_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1719_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1711_);
                    v___x_1713_ = v_reuseFailAlloc_1719_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1714_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1714_, 0, v___x_1710_);
                crate::leanh::lean_ctor_set(v___x_1714_, 1, v___x_1713_);
                crate::leanh::lean_inc(v___y_1709_);
                v___x_1715_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1715_, 0, v___y_1709_);
                crate::leanh::lean_ctor_set(v___x_1715_, 1, v___x_1714_);
                v___x_1716_ = 0;
                v___x_1717_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1717_, 0, v___x_1715_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1717_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1716_,
                );
                v___x_1718_ = l_Repr_addAppParen(v___x_1717_, v_prec_1703_);
                return v___x_1718_;
            }
            4 => {
                v___x_1729_ = l_Lean_Widget_instReprTaggedText_repr___redArg___closed__7;
                v___x_1730_ = l_Array_repr___redArg(v_localinst_1726_, v_a_1725_);
                v___x_1731_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1731_, 0, v___x_1729_);
                crate::leanh::lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                crate::leanh::lean_inc(v___y_1728_);
                v___x_1732_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1732_, 0, v___y_1728_);
                crate::leanh::lean_ctor_set(v___x_1732_, 1, v___x_1731_);
                v___x_1733_ = 0;
                v___x_1734_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1734_, 0, v___x_1732_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1734_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1733_,
                );
                v___x_1735_ = l_Repr_addAppParen(v___x_1734_, v_prec_1703_);
                return v___x_1735_;
            }
            5 => {
                v___x_1745_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1761_ = lean_nat_dec_le(v___x_1745_, v_prec_1703_);
                if v___x_1761_ == 0 {
                    v___x_1762_ = crate::leanh::lean_obj_once(
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
                    v___x_1763_ = crate::leanh::lean_obj_once(
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
                v___x_1748_ = crate::leanh::lean_box(1);
                v___x_1749_ = l_Lean_Widget_instReprTaggedText_repr___redArg___closed__10;
                crate::leanh::lean_inc_ref(v_inst_1701_);
                v___x_1750_ = crate::leanh::lean_apply_2(v_inst_1701_, v_a_1740_, v___x_1745_);
                if v_isShared_1744_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1743_, 5);
                    crate::leanh::lean_ctor_set(v___x_1743_, 1, v___x_1750_);
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1749_);
                    v___x_1752_ = v___x_1743_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1750_);
                    v___x_1752_ = v_reuseFailAlloc_1760_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1753_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1752_);
                crate::leanh::lean_ctor_set(v___x_1753_, 1, v___x_1748_);
                v___x_1754_ = l_Lean_Widget_instReprTaggedText_repr___redArg(
                    v_inst_1701_,
                    v_a_1741_,
                    v___x_1745_,
                );
                v___x_1755_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1755_, 0, v___x_1753_);
                crate::leanh::lean_ctor_set(v___x_1755_, 1, v___x_1754_);
                crate::leanh::lean_inc(v___y_1747_);
                v___x_1756_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1756_, 0, v___y_1747_);
                crate::leanh::lean_ctor_set(v___x_1756_, 1, v___x_1755_);
                v___x_1757_ = 0;
                v___x_1758_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1756_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1758_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_00_u03b1_1765_: *mut crate::leanh::LeanObject,
    mut v_inst_1766_: *mut crate::leanh::LeanObject,
    mut v_x_1767_: *mut crate::leanh::LeanObject,
    mut v_prec_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1769_ =
        l_Lean_Widget_instReprTaggedText_repr___redArg(v_inst_1766_, v_x_1767_, v_prec_1768_);
    return v___x_1769_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText_repr___boxed(
    mut v_00_u03b1_1770_: *mut crate::leanh::LeanObject,
    mut v_inst_1771_: *mut crate::leanh::LeanObject,
    mut v_x_1772_: *mut crate::leanh::LeanObject,
    mut v_prec_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1774_ = l_Lean_Widget_instReprTaggedText_repr(
        v_00_u03b1_1770_,
        v_inst_1771_,
        v_x_1772_,
        v_prec_1773_,
    );
    crate::leanh::lean_dec(v_prec_1773_);
    return v_res_1774_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText___redArg(
    mut v_inst_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1776_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_instReprTaggedText_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1776_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1776_, 1, v_inst_1775_);
    return v___x_1776_;
}
pub unsafe fn l_Lean_Widget_instReprTaggedText(
    mut v_00_u03b1_1777_: *mut crate::leanh::LeanObject,
    mut v_inst_1778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1779_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_instReprTaggedText_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1779_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1779_, 1, v_inst_1778_);
    return v___x_1779_;
}
pub unsafe fn l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(
    mut v_inst_1789_: *mut crate::leanh::LeanObject,
    mut v_json_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_a_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut v_a_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut v_a_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1863_: u8 = 0;
    let mut v_a_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1867_: u8 = 0;
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v_a_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localinst_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1894_: u8 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1898_: u8 = 0;
    let mut v_a_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_json_1790_);
                v___x_1791_ = l_Lean_Json_getTag_x3f(v_json_1790_);
                if crate::leanh::lean_obj_tag(v___x_1791_) == 0 {
                    crate::leanh::lean_dec(v_json_1790_);
                    crate::leanh::lean_dec_ref(v_inst_1789_);
                    v___x_1792_ =
                        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__1;
                    return v___x_1792_;
                } else {
                    v_val_1793_ = crate::leanh::lean_ctor_get(v___x_1791_, 0);
                    v_isSharedCheck_1910_ = (!crate::leanh::lean_is_exclusive(v___x_1791_)) as u8;
                    if v_isSharedCheck_1910_ == 0 {
                        v___x_1795_ = v___x_1791_;
                        v_isShared_1796_ = v_isSharedCheck_1910_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1793_);
                        crate::leanh::lean_dec(v___x_1791_);
                        v___x_1795_ = crate::leanh::lean_box(0);
                        v_isShared_1796_ = v_isSharedCheck_1910_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1797_ = crate::leanh::lean_box(0);
                v___x_1798_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2;
                v___x_1799_ = lean_string_dec_eq(v_val_1793_, v___x_1798_);
                if v___x_1799_ == 0 {
                    v___x_1800_ =
                        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3;
                    v___x_1801_ = lean_string_dec_eq(v_val_1793_, v___x_1800_);
                    if v___x_1801_ == 0 {
                        crate::leanh::lean_del_object(v___x_1795_);
                        v___x_1802_ =
                            l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4;
                        v___x_1803_ = lean_string_dec_eq(v_val_1793_, v___x_1802_);
                        crate::leanh::lean_dec(v_val_1793_);
                        if v___x_1803_ == 0 {
                            crate::leanh::lean_dec(v_json_1790_);
                            crate::leanh::lean_dec_ref(v_inst_1789_);
                            v___x_1804_ =
                                l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__6;
                            return v___x_1804_;
                        } else {
                            v___x_1805_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_1806_ = crate::leanh::lean_box(0);
                            v___x_1807_ = l_Lean_Json_parseCtorFields(
                                v_json_1790_,
                                v___x_1802_,
                                v___x_1805_,
                                v___x_1806_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1807_) == 0 {
                                crate::leanh::lean_dec_ref(v_inst_1789_);
                                v_a_1808_ = crate::leanh::lean_ctor_get(v___x_1807_, 0);
                                v_isSharedCheck_1815_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1807_)) as u8;
                                if v_isSharedCheck_1815_ == 0 {
                                    v___x_1810_ = v___x_1807_;
                                    v_isShared_1811_ = v_isSharedCheck_1815_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1808_);
                                    crate::leanh::lean_dec(v___x_1807_);
                                    v___x_1810_ = crate::leanh::lean_box(0);
                                    v_isShared_1811_ = v_isSharedCheck_1815_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_1816_ = crate::leanh::lean_ctor_get(v___x_1807_, 0);
                                crate::leanh::lean_inc(v_a_1816_);
                                crate::leanh::lean_dec_ref_known(v___x_1807_, 1);
                                v___x_1817_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_1818_ =
                                    lean_array_get_borrowed(v___x_1797_, v_a_1816_, v___x_1817_);
                                crate::leanh::lean_inc_ref(v_inst_1789_);
                                crate::leanh::lean_inc(v___x_1818_);
                                v___x_1819_ = crate::leanh::lean_apply_1(v_inst_1789_, v___x_1818_);
                                if crate::leanh::lean_obj_tag(v___x_1819_) == 0 {
                                    crate::leanh::lean_dec(v_a_1816_);
                                    crate::leanh::lean_dec_ref(v_inst_1789_);
                                    v_a_1820_ = crate::leanh::lean_ctor_get(v___x_1819_, 0);
                                    v_isSharedCheck_1827_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1819_)) as u8;
                                    if v_isSharedCheck_1827_ == 0 {
                                        v___x_1822_ = v___x_1819_;
                                        v_isShared_1823_ = v_isSharedCheck_1827_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1820_);
                                        crate::leanh::lean_dec(v___x_1819_);
                                        v___x_1822_ = crate::leanh::lean_box(0);
                                        v_isShared_1823_ = v_isSharedCheck_1827_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v_a_1828_ = crate::leanh::lean_ctor_get(v___x_1819_, 0);
                                    crate::leanh::lean_inc(v_a_1828_);
                                    crate::leanh::lean_dec_ref_known(v___x_1819_, 1);
                                    v___x_1829_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1830_ =
                                        lean_array_get(v___x_1797_, v_a_1816_, v___x_1829_);
                                    crate::leanh::lean_dec(v_a_1816_);
                                    v___x_1831_ =
                                        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(
                                            v_inst_1789_,
                                            v___x_1830_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_1831_) == 0 {
                                        crate::leanh::lean_dec(v_a_1828_);
                                        return v___x_1831_;
                                    } else {
                                        v_a_1832_ = crate::leanh::lean_ctor_get(v___x_1831_, 0);
                                        v_isSharedCheck_1840_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1831_)) as u8;
                                        if v_isSharedCheck_1840_ == 0 {
                                            v___x_1834_ = v___x_1831_;
                                            v_isShared_1835_ = v_isSharedCheck_1840_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1832_);
                                            crate::leanh::lean_dec(v___x_1831_);
                                            v___x_1834_ = crate::leanh::lean_box(0);
                                            v_isShared_1835_ = v_isSharedCheck_1840_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1793_);
                        crate::leanh::lean_dec_ref(v_inst_1789_);
                        v___x_1841_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1842_ = crate::leanh::lean_box(0);
                        v___x_1843_ = l_Lean_Json_parseCtorFields(
                            v_json_1790_,
                            v___x_1800_,
                            v___x_1841_,
                            v___x_1842_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1843_) == 0 {
                            crate::leanh::lean_del_object(v___x_1795_);
                            v_a_1844_ = crate::leanh::lean_ctor_get(v___x_1843_, 0);
                            v_isSharedCheck_1851_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1843_)) as u8;
                            if v_isSharedCheck_1851_ == 0 {
                                v___x_1846_ = v___x_1843_;
                                v_isShared_1847_ = v_isSharedCheck_1851_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1844_);
                                crate::leanh::lean_dec(v___x_1843_);
                                v___x_1846_ = crate::leanh::lean_box(0);
                                v_isShared_1847_ = v_isSharedCheck_1851_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_1852_ = crate::leanh::lean_ctor_get(v___x_1843_, 0);
                            crate::leanh::lean_inc(v_a_1852_);
                            crate::leanh::lean_dec_ref_known(v___x_1843_, 1);
                            v___x_1853_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1854_ = lean_array_get(v___x_1797_, v_a_1852_, v___x_1853_);
                            crate::leanh::lean_dec(v_a_1852_);
                            v___x_1855_ = l_Lean_Json_getStr_x3f(v___x_1854_);
                            if crate::leanh::lean_obj_tag(v___x_1855_) == 0 {
                                crate::leanh::lean_del_object(v___x_1795_);
                                v_a_1856_ = crate::leanh::lean_ctor_get(v___x_1855_, 0);
                                v_isSharedCheck_1863_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1855_)) as u8;
                                if v_isSharedCheck_1863_ == 0 {
                                    v___x_1858_ = v___x_1855_;
                                    v_isShared_1859_ = v_isSharedCheck_1863_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1856_);
                                    crate::leanh::lean_dec(v___x_1855_);
                                    v___x_1858_ = crate::leanh::lean_box(0);
                                    v_isShared_1859_ = v_isSharedCheck_1863_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                v_a_1864_ = crate::leanh::lean_ctor_get(v___x_1855_, 0);
                                v_isSharedCheck_1874_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1855_)) as u8;
                                if v_isSharedCheck_1874_ == 0 {
                                    v___x_1866_ = v___x_1855_;
                                    v_isShared_1867_ = v_isSharedCheck_1874_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1864_);
                                    crate::leanh::lean_dec(v___x_1855_);
                                    v___x_1866_ = crate::leanh::lean_box(0);
                                    v_isShared_1867_ = v_isSharedCheck_1874_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_val_1793_);
                    v___x_1875_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1876_ = crate::leanh::lean_box(0);
                    v___x_1877_ = l_Lean_Json_parseCtorFields(
                        v_json_1790_,
                        v___x_1798_,
                        v___x_1875_,
                        v___x_1876_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1877_) == 0 {
                        crate::leanh::lean_del_object(v___x_1795_);
                        crate::leanh::lean_dec_ref(v_inst_1789_);
                        v_a_1878_ = crate::leanh::lean_ctor_get(v___x_1877_, 0);
                        v_isSharedCheck_1885_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1877_)) as u8;
                        if v_isSharedCheck_1885_ == 0 {
                            v___x_1880_ = v___x_1877_;
                            v_isShared_1881_ = v_isSharedCheck_1885_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1878_);
                            crate::leanh::lean_dec(v___x_1877_);
                            v___x_1880_ = crate::leanh::lean_box(0);
                            v_isShared_1881_ = v_isSharedCheck_1885_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v_a_1886_ = crate::leanh::lean_ctor_get(v___x_1877_, 0);
                        crate::leanh::lean_inc(v_a_1886_);
                        crate::leanh::lean_dec_ref_known(v___x_1877_, 1);
                        v_localinst_1887_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        crate::leanh::lean_closure_set(v_localinst_1887_, 0, v_inst_1789_);
                        v___x_1888_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1889_ = lean_array_get(v___x_1797_, v_a_1886_, v___x_1888_);
                        crate::leanh::lean_dec(v_a_1886_);
                        v___x_1890_ = l_Array_fromJson_x3f___redArg(v_localinst_1887_, v___x_1889_);
                        if crate::leanh::lean_obj_tag(v___x_1890_) == 0 {
                            crate::leanh::lean_del_object(v___x_1795_);
                            v_a_1891_ = crate::leanh::lean_ctor_get(v___x_1890_, 0);
                            v_isSharedCheck_1898_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1890_)) as u8;
                            if v_isSharedCheck_1898_ == 0 {
                                v___x_1893_ = v___x_1890_;
                                v_isShared_1894_ = v_isSharedCheck_1898_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1891_);
                                crate::leanh::lean_dec(v___x_1890_);
                                v___x_1893_ = crate::leanh::lean_box(0);
                                v_isShared_1894_ = v_isSharedCheck_1898_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v_a_1899_ = crate::leanh::lean_ctor_get(v___x_1890_, 0);
                            v_isSharedCheck_1909_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1890_)) as u8;
                            if v_isSharedCheck_1909_ == 0 {
                                v___x_1901_ = v___x_1890_;
                                v_isShared_1902_ = v_isSharedCheck_1909_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1899_);
                                crate::leanh::lean_dec(v___x_1890_);
                                v___x_1901_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1814_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
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
                    v_reuseFailAlloc_1826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
                    v___x_1825_ = v_reuseFailAlloc_1826_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1825_;
            }
            6 => {
                v___x_1836_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1836_, 0, v_a_1828_);
                crate::leanh::lean_ctor_set(v___x_1836_, 1, v_a_1832_);
                if v_isShared_1835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1834_, 0, v___x_1836_);
                    v___x_1838_ = v___x_1834_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
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
                    v_reuseFailAlloc_1850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
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
                    v_reuseFailAlloc_1862_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_1795_, 0);
                    crate::leanh::lean_ctor_set(v___x_1795_, 0, v_a_1864_);
                    v___x_1869_ = v___x_1795_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1864_);
                    v___x_1869_ = v_reuseFailAlloc_1873_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_1867_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1869_);
                    v___x_1871_ = v___x_1866_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
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
                    v_reuseFailAlloc_1884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
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
                    v_reuseFailAlloc_1897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
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
                    crate::leanh::lean_ctor_set(v___x_1795_, 0, v_a_1899_);
                    v___x_1904_ = v___x_1795_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1899_);
                    v___x_1904_ = v_reuseFailAlloc_1908_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1901_, 0, v___x_1904_);
                    v___x_1906_ = v___x_1901_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
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
    mut v_00_u03b1_1911_: *mut crate::leanh::LeanObject,
    mut v_inst_1912_: *mut crate::leanh::LeanObject,
    mut v_json_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ =
        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v_inst_1912_, v_json_1913_);
    return v___x_1914_;
}
pub unsafe fn l_Lean_Widget_instFromJsonTaggedText___redArg(
    mut v_inst_1915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_instFromJsonTaggedText_fromJson as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1916_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1916_, 1, v_inst_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_Widget_instFromJsonTaggedText(
    mut v_00_u03b1_1917_: *mut crate::leanh::LeanObject,
    mut v_inst_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_instFromJsonTaggedText_fromJson as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1919_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1919_, 1, v_inst_1918_);
    return v___x_1919_;
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText_toJson___redArg(
    mut v_inst_1920_: *mut crate::leanh::LeanObject,
    mut v_x_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1934_: u8 = 0;
    let mut v_a_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localinst_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1947_: u8 = 0;
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1921_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_inst_1920_);
                    v_a_1922_ = crate::leanh::lean_ctor_get(v_x_1921_, 0);
                    v_isSharedCheck_1934_ = (!crate::leanh::lean_is_exclusive(v_x_1921_)) as u8;
                    if v_isSharedCheck_1934_ == 0 {
                        v___x_1924_ = v_x_1921_;
                        v_isShared_1925_ = v_isSharedCheck_1934_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1922_);
                        crate::leanh::lean_dec(v_x_1921_);
                        v___x_1924_ = crate::leanh::lean_box(0);
                        v_isShared_1925_ = v_isSharedCheck_1934_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_1935_ = crate::leanh::lean_ctor_get(v_x_1921_, 0);
                    crate::leanh::lean_inc_ref(v_a_1935_);
                    crate::leanh::lean_dec_ref_known(v_x_1921_, 1);
                    v_localinst_1936_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Widget_instToJsonTaggedText_toJson___redArg
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v_localinst_1936_, 0, v_inst_1920_);
                    v___x_1937_ =
                        l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__2;
                    v___x_1938_ = l_Array_toJson___redArg(v_localinst_1936_, v_a_1935_);
                    v___x_1939_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1939_, 0, v___x_1937_);
                    crate::leanh::lean_ctor_set(v___x_1939_, 1, v___x_1938_);
                    v___x_1940_ = crate::leanh::lean_box(0);
                    v___x_1941_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1941_, 0, v___x_1939_);
                    crate::leanh::lean_ctor_set(v___x_1941_, 1, v___x_1940_);
                    v___x_1942_ = l_Lean_Json_mkObj(v___x_1941_);
                    crate::leanh::lean_dec_ref_known(v___x_1941_, 2);
                    return v___x_1942_;
                }
                _ => {
                    v_a_1943_ = crate::leanh::lean_ctor_get(v_x_1921_, 0);
                    v_a_1944_ = crate::leanh::lean_ctor_get(v_x_1921_, 1);
                    v_isSharedCheck_1962_ = (!crate::leanh::lean_is_exclusive(v_x_1921_)) as u8;
                    if v_isSharedCheck_1962_ == 0 {
                        v___x_1946_ = v_x_1921_;
                        v_isShared_1947_ = v_isSharedCheck_1962_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1944_);
                        crate::leanh::lean_inc(v_a_1943_);
                        crate::leanh::lean_dec(v_x_1921_);
                        v___x_1946_ = crate::leanh::lean_box(0);
                        v_isShared_1947_ = v_isSharedCheck_1962_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1926_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__3;
                if v_isShared_1925_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1924_, 3);
                    v___x_1928_ = v___x_1924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1933_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1922_);
                    v___x_1928_ = v_reuseFailAlloc_1933_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1929_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1929_, 0, v___x_1926_);
                crate::leanh::lean_ctor_set(v___x_1929_, 1, v___x_1928_);
                v___x_1930_ = crate::leanh::lean_box(0);
                v___x_1931_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1931_, 0, v___x_1929_);
                crate::leanh::lean_ctor_set(v___x_1931_, 1, v___x_1930_);
                v___x_1932_ = l_Lean_Json_mkObj(v___x_1931_);
                crate::leanh::lean_dec_ref_known(v___x_1931_, 2);
                return v___x_1932_;
            }
            3 => {
                v___x_1948_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg___closed__4;
                crate::leanh::lean_inc_ref(v_inst_1920_);
                v___x_1949_ = crate::leanh::lean_apply_1(v_inst_1920_, v_a_1943_);
                v___x_1950_ =
                    l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_1920_, v_a_1944_);
                v___x_1951_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1952_ = lean_mk_empty_array_with_capacity(v___x_1951_);
                v___x_1953_ = lean_array_push(v___x_1952_, v___x_1949_);
                v___x_1954_ = lean_array_push(v___x_1953_, v___x_1950_);
                v___x_1955_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1955_, 0, v___x_1954_);
                if v_isShared_1947_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1946_, 0);
                    crate::leanh::lean_ctor_set(v___x_1946_, 1, v___x_1955_);
                    crate::leanh::lean_ctor_set(v___x_1946_, 0, v___x_1948_);
                    v___x_1957_ = v___x_1946_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1961_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1955_);
                    v___x_1957_ = v_reuseFailAlloc_1961_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1958_ = crate::leanh::lean_box(0);
                v___x_1959_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1959_, 0, v___x_1957_);
                crate::leanh::lean_ctor_set(v___x_1959_, 1, v___x_1958_);
                v___x_1960_ = l_Lean_Json_mkObj(v___x_1959_);
                crate::leanh::lean_dec_ref_known(v___x_1959_, 2);
                return v___x_1960_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText_toJson(
    mut v_00_u03b1_1963_: *mut crate::leanh::LeanObject,
    mut v_inst_1964_: *mut crate::leanh::LeanObject,
    mut v_x_1965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1966_ = l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v_inst_1964_, v_x_1965_);
    return v___x_1966_;
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText___redArg(
    mut v_inst_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1968_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_instToJsonTaggedText_toJson as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1968_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1968_, 1, v_inst_1967_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText(
    mut v_00_u03b1_1969_: *mut crate::leanh::LeanObject,
    mut v_inst_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1971_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_instToJsonTaggedText_toJson as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1971_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1971_, 1, v_inst_1970_);
    return v___x_1971_;
}
pub unsafe fn l_Lean_Widget_TaggedText_appendText___redArg(
    mut v_s_u2080_1972_: *mut crate::leanh::LeanObject,
    mut v_x_1973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut v_a_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1973_) {
                0 => {
                    v_a_1974_ = crate::leanh::lean_ctor_get(v_x_1973_, 0);
                    v_isSharedCheck_1982_ = (!crate::leanh::lean_is_exclusive(v_x_1973_)) as u8;
                    if v_isSharedCheck_1982_ == 0 {
                        v___x_1976_ = v_x_1973_;
                        v_isShared_1977_ = v_isSharedCheck_1982_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1974_);
                        crate::leanh::lean_dec(v_x_1973_);
                        v___x_1976_ = crate::leanh::lean_box(0);
                        v_isShared_1977_ = v_isSharedCheck_1982_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_1983_ = crate::leanh::lean_ctor_get(v_x_1973_, 0);
                    v_isSharedCheck_2010_ = (!crate::leanh::lean_is_exclusive(v_x_1973_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_1985_ = v_x_1973_;
                        v_isShared_1986_ = v_isSharedCheck_2010_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1983_);
                        crate::leanh::lean_dec(v_x_1973_);
                        v___x_1985_ = crate::leanh::lean_box(0);
                        v_isShared_1986_ = v_isSharedCheck_2010_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_2011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2011_, 0, v_s_u2080_1972_);
                    v___x_2012_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2013_ = lean_mk_empty_array_with_capacity(v___x_2012_);
                    v___x_2014_ = lean_array_push(v___x_2013_, v_x_1973_);
                    v___x_2015_ = lean_array_push(v___x_2014_, v___x_2011_);
                    v___x_2016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2016_, 0, v___x_2015_);
                    return v___x_2016_;
                }
            },
            1 => {
                v___x_1978_ = lean_string_append(v_a_1974_, v_s_u2080_1972_);
                crate::leanh::lean_dec_ref(v_s_u2080_1972_);
                if v_isShared_1977_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1976_, 0, v___x_1978_);
                    v___x_1980_ = v___x_1976_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
                    v___x_1980_ = v_reuseFailAlloc_1981_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1980_;
            }
            3 => {
                v___x_1987_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0_once),
                    _init_l_Lean_Widget_instInhabitedTaggedText___closed__0,
                );
                v___x_1988_ = lean_array_get_size(v_a_1983_);
                v___x_1989_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1990_ = lean_nat_sub(v___x_1988_, v___x_1989_);
                v___x_1991_ = lean_array_get(v___x_1987_, v_a_1983_, v___x_1990_);
                if crate::leanh::lean_obj_tag(v___x_1991_) == 0 {
                    v_a_1992_ = crate::leanh::lean_ctor_get(v___x_1991_, 0);
                    v_isSharedCheck_2004_ = (!crate::leanh::lean_is_exclusive(v___x_1991_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v___x_1994_ = v___x_1991_;
                        v_isShared_1995_ = v_isSharedCheck_2004_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1992_);
                        crate::leanh::lean_dec(v___x_1991_);
                        v___x_1994_ = crate::leanh::lean_box(0);
                        v_isShared_1995_ = v_isSharedCheck_2004_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1991_);
                    crate::leanh::lean_dec(v___x_1990_);
                    if v_isShared_1986_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1985_, 0);
                        crate::leanh::lean_ctor_set(v___x_1985_, 0, v_s_u2080_1972_);
                        v___x_2006_ = v___x_1985_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_s_u2080_1972_);
                        v___x_2006_ = v_reuseFailAlloc_2009_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1996_ = lean_string_append(v_a_1992_, v_s_u2080_1972_);
                crate::leanh::lean_dec_ref(v_s_u2080_1972_);
                if v_isShared_1995_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1994_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1994_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1996_);
                    v___x_1998_ = v_reuseFailAlloc_2003_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1999_ = lean_array_set(v_a_1983_, v___x_1990_, v___x_1998_);
                crate::leanh::lean_dec(v___x_1990_);
                if v_isShared_1986_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1985_, 0, v___x_1999_);
                    v___x_2001_ = v___x_1985_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
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
                v___x_2008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2008_, 0, v___x_2007_);
                return v___x_2008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_appendText(
    mut v_00_u03b1_2017_: *mut crate::leanh::LeanObject,
    mut v_s_u2080_2018_: *mut crate::leanh::LeanObject,
    mut v_x_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_u2080_2018_, v_x_2019_);
    return v___x_2020_;
}
pub unsafe fn l_Lean_Widget_TaggedText_appendTag___redArg(
    mut v_acc_2021_: *mut crate::leanh::LeanObject,
    mut v_t_u2080_2022_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_2023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2041_: u8 = 0;
    let mut v_a_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: u8 = 0;
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_acc_2021_) {
                1 => {
                    v_a_2032_ = crate::leanh::lean_ctor_get(v_acc_2021_, 0);
                    v_isSharedCheck_2041_ = (!crate::leanh::lean_is_exclusive(v_acc_2021_)) as u8;
                    if v_isSharedCheck_2041_ == 0 {
                        v___x_2034_ = v_acc_2021_;
                        v_isShared_2035_ = v_isSharedCheck_2041_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2032_);
                        crate::leanh::lean_dec(v_acc_2021_);
                        v___x_2034_ = crate::leanh::lean_box(0);
                        v_isShared_2035_ = v_isSharedCheck_2041_;
                        state = 2;
                        continue;
                    }
                }
                0 => {
                    v_a_2042_ = crate::leanh::lean_ctor_get(v_acc_2021_, 0);
                    v___x_2043_ = l_Lean_Widget_instInhabitedTaggedText_default___closed__0;
                    v___x_2044_ = lean_string_dec_eq(v_a_2042_, v___x_2043_);
                    if v___x_2044_ == 0 {
                        v_a_2025_ = v_acc_2021_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_acc_2021_, 1);
                        v___x_2045_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2045_, 0, v_t_u2080_2022_);
                        crate::leanh::lean_ctor_set(v___x_2045_, 1, v_a_u2080_2023_);
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
                v___x_2026_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2026_, 0, v_t_u2080_2022_);
                crate::leanh::lean_ctor_set(v___x_2026_, 1, v_a_u2080_2023_);
                v___x_2027_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2028_ = lean_mk_empty_array_with_capacity(v___x_2027_);
                v___x_2029_ = lean_array_push(v___x_2028_, v_a_2025_);
                v___x_2030_ = lean_array_push(v___x_2029_, v___x_2026_);
                v___x_2031_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2031_, 0, v___x_2030_);
                return v___x_2031_;
            }
            2 => {
                v___x_2036_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2036_, 0, v_t_u2080_2022_);
                crate::leanh::lean_ctor_set(v___x_2036_, 1, v_a_u2080_2023_);
                v___x_2037_ = lean_array_push(v_a_2032_, v___x_2036_);
                if v_isShared_2035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2034_, 0, v___x_2037_);
                    v___x_2039_ = v___x_2034_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
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
    mut v_00_u03b1_2046_: *mut crate::leanh::LeanObject,
    mut v_acc_2047_: *mut crate::leanh::LeanObject,
    mut v_t_u2080_2048_: *mut crate::leanh::LeanObject,
    mut v_a_u2080_2049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ =
        l_Lean_Widget_TaggedText_appendTag___redArg(v_acc_2047_, v_t_u2080_2048_, v_a_u2080_2049_);
    return v___x_2050_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(
    mut v_f_2051_: *mut crate::leanh::LeanObject,
    mut v_sz_2052_: usize,
    mut v_i_2053_: usize,
    mut v_bs_2054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2055_: u8 = 0;
    let mut v_v_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: usize = 0;
    let mut v___x_2061_: usize = 0;
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2055_ = lean_usize_dec_lt(v_i_2053_, v_sz_2052_);
                if v___x_2055_ == 0 {
                    crate::leanh::lean_dec(v_f_2051_);
                    return v_bs_2054_;
                } else {
                    v_v_2056_ = lean_array_uget(v_bs_2054_, v_i_2053_);
                    v___x_2057_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2058_ = lean_array_uset(v_bs_2054_, v_i_2053_, v___x_2057_);
                    crate::leanh::lean_inc(v_f_2051_);
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
    mut v_f_2064_: *mut crate::leanh::LeanObject,
    mut v_x_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut v_a_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v_sz_2078_: usize = 0;
    let mut v___x_2079_: usize = 0;
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_a_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2089_: u8 = 0;
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2065_) {
                0 => {
                    crate::leanh::lean_dec(v_f_2064_);
                    v_a_2066_ = crate::leanh::lean_ctor_get(v_x_2065_, 0);
                    v_isSharedCheck_2073_ = (!crate::leanh::lean_is_exclusive(v_x_2065_)) as u8;
                    if v_isSharedCheck_2073_ == 0 {
                        v___x_2068_ = v_x_2065_;
                        v_isShared_2069_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2066_);
                        crate::leanh::lean_dec(v_x_2065_);
                        v___x_2068_ = crate::leanh::lean_box(0);
                        v_isShared_2069_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_2074_ = crate::leanh::lean_ctor_get(v_x_2065_, 0);
                    v_isSharedCheck_2084_ = (!crate::leanh::lean_is_exclusive(v_x_2065_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v___x_2076_ = v_x_2065_;
                        v_isShared_2077_ = v_isSharedCheck_2084_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2074_);
                        crate::leanh::lean_dec(v_x_2065_);
                        v___x_2076_ = crate::leanh::lean_box(0);
                        v_isShared_2077_ = v_isSharedCheck_2084_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_2085_ = crate::leanh::lean_ctor_get(v_x_2065_, 0);
                    v_a_2086_ = crate::leanh::lean_ctor_get(v_x_2065_, 1);
                    v_isSharedCheck_2095_ = (!crate::leanh::lean_is_exclusive(v_x_2065_)) as u8;
                    if v_isSharedCheck_2095_ == 0 {
                        v___x_2088_ = v_x_2065_;
                        v_isShared_2089_ = v_isSharedCheck_2095_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2086_);
                        crate::leanh::lean_inc(v_a_2085_);
                        crate::leanh::lean_dec(v_x_2065_);
                        v___x_2088_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
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
                    crate::leanh::lean_ctor_set(v___x_2076_, 0, v___x_2080_);
                    v___x_2082_ = v___x_2076_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
                    v___x_2082_ = v_reuseFailAlloc_2083_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2082_;
            }
            5 => {
                crate::leanh::lean_inc(v_f_2064_);
                v___x_2090_ = crate::leanh::lean_apply_1(v_f_2064_, v_a_2085_);
                v___x_2091_ = l_Lean_Widget_TaggedText_map___redArg(v_f_2064_, v_a_2086_);
                if v_isShared_2089_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2088_, 1, v___x_2091_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_2090_);
                    v___x_2093_ = v___x_2088_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2094_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2091_);
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
    mut v_f_2096_: *mut crate::leanh::LeanObject,
    mut v_sz_2097_: *mut crate::leanh::LeanObject,
    mut v_i_2098_: *mut crate::leanh::LeanObject,
    mut v_bs_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2100_: usize = 0;
    let mut v_i_boxed_2101_: usize = 0;
    let mut v_res_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2100_ = crate::leanh::lean_unbox_usize(v_sz_2097_);
    crate::leanh::lean_dec(v_sz_2097_);
    v_i_boxed_2101_ = crate::leanh::lean_unbox_usize(v_i_2098_);
    crate::leanh::lean_dec(v_i_2098_);
    v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_2096_, v_sz_boxed_2100_, v_i_boxed_2101_, v_bs_2099_);
    return v_res_2102_;
}
pub unsafe fn l_Lean_Widget_TaggedText_map(
    mut v_00_u03b1_2103_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2104_: *mut crate::leanh::LeanObject,
    mut v_f_2105_: *mut crate::leanh::LeanObject,
    mut v_x_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2107_ = l_Lean_Widget_TaggedText_map___redArg(v_f_2105_, v_x_2106_);
    return v___x_2107_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(
    mut v_00_u03b1_2108_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2109_: *mut crate::leanh::LeanObject,
    mut v_f_2110_: *mut crate::leanh::LeanObject,
    mut v_sz_2111_: usize,
    mut v_i_2112_: usize,
    mut v_bs_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___redArg(v_f_2110_, v_sz_2111_, v_i_2112_, v_bs_2113_);
    return v___x_2114_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0___boxed(
    mut v_00_u03b1_2115_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2116_: *mut crate::leanh::LeanObject,
    mut v_f_2117_: *mut crate::leanh::LeanObject,
    mut v_sz_2118_: *mut crate::leanh::LeanObject,
    mut v_i_2119_: *mut crate::leanh::LeanObject,
    mut v_bs_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2121_: usize = 0;
    let mut v_i_boxed_2122_: usize = 0;
    let mut v_res_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2121_ = crate::leanh::lean_unbox_usize(v_sz_2118_);
    crate::leanh::lean_dec(v_sz_2118_);
    v_i_boxed_2122_ = crate::leanh::lean_unbox_usize(v_i_2119_);
    crate::leanh::lean_dec(v_i_2119_);
    v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_map_spec__0(v_00_u03b1_2115_, v_00_u03b2_2116_, v_f_2117_, v_sz_boxed_2121_, v_i_boxed_2122_, v_bs_2120_);
    return v_res_2123_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___redArg___lam__0(
    mut v_toPure_2124_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2126_, 0, v_____do__lift_2125_);
    v___x_2127_ =
        crate::leanh::lean_apply_2(v_toPure_2124_, crate::leanh::lean_box(0), v___x_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___redArg___lam__1(
    mut v_____do__lift_2128_: *mut crate::leanh::LeanObject,
    mut v_toPure_2129_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2131_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2131_, 0, v_____do__lift_2128_);
    crate::leanh::lean_ctor_set(v___x_2131_, 1, v_____do__lift_2130_);
    v___x_2132_ =
        crate::leanh::lean_apply_2(v_toPure_2129_, crate::leanh::lean_box(0), v___x_2131_);
    return v___x_2132_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___redArg(
    mut v_inst_2133_: *mut crate::leanh::LeanObject,
    mut v_f_2134_: *mut crate::leanh::LeanObject,
    mut v_x_2135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2141_: u8 = 0;
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v_toApplicative_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2153_: usize = 0;
    let mut v___x_2154_: usize = 0;
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2135_) {
                0 => {
                    v_toApplicative_2136_ = crate::leanh::lean_ctor_get(v_inst_2133_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_2136_);
                    crate::leanh::lean_dec(v_f_2134_);
                    crate::leanh::lean_dec_ref(v_inst_2133_);
                    v_toPure_2137_ = crate::leanh::lean_ctor_get(v_toApplicative_2136_, 1);
                    crate::leanh::lean_inc(v_toPure_2137_);
                    crate::leanh::lean_dec_ref(v_toApplicative_2136_);
                    v_a_2138_ = crate::leanh::lean_ctor_get(v_x_2135_, 0);
                    v_isSharedCheck_2146_ = (!crate::leanh::lean_is_exclusive(v_x_2135_)) as u8;
                    if v_isSharedCheck_2146_ == 0 {
                        v___x_2140_ = v_x_2135_;
                        v_isShared_2141_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2138_);
                        crate::leanh::lean_dec(v_x_2135_);
                        v___x_2140_ = crate::leanh::lean_box(0);
                        v_isShared_2141_ = v_isSharedCheck_2146_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_toApplicative_2147_ = crate::leanh::lean_ctor_get(v_inst_2133_, 0);
                    v_toBind_2148_ = crate::leanh::lean_ctor_get(v_inst_2133_, 1);
                    crate::leanh::lean_inc(v_toBind_2148_);
                    v_toPure_2149_ = crate::leanh::lean_ctor_get(v_toApplicative_2147_, 1);
                    v_a_2150_ = crate::leanh::lean_ctor_get(v_x_2135_, 0);
                    crate::leanh::lean_inc_ref(v_a_2150_);
                    crate::leanh::lean_dec_ref_known(v_x_2135_, 1);
                    crate::leanh::lean_inc(v_toPure_2149_);
                    v___f_2151_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_mapM___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2151_, 0, v_toPure_2149_);
                    crate::leanh::lean_inc_ref(v_inst_2133_);
                    v___x_2152_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_mapM___redArg as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_2152_, 0, v_inst_2133_);
                    crate::leanh::lean_closure_set(v___x_2152_, 1, v_f_2134_);
                    v_sz_2153_ = lean_array_size(v_a_2150_);
                    v___x_2154_ = 0usize;
                    v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_2133_,
                        v___x_2152_,
                        v_sz_2153_,
                        v___x_2154_,
                        v_a_2150_,
                    );
                    v___x_2156_ = crate::leanh::lean_apply_4(
                        v_toBind_2148_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_2155_,
                        v___f_2151_,
                    );
                    return v___x_2156_;
                }
                _ => {
                    v_toApplicative_2157_ = crate::leanh::lean_ctor_get(v_inst_2133_, 0);
                    v_toBind_2158_ = crate::leanh::lean_ctor_get(v_inst_2133_, 1);
                    crate::leanh::lean_inc_n(v_toBind_2158_, 2);
                    v_toPure_2159_ = crate::leanh::lean_ctor_get(v_toApplicative_2157_, 1);
                    crate::leanh::lean_inc(v_toPure_2159_);
                    v_a_2160_ = crate::leanh::lean_ctor_get(v_x_2135_, 0);
                    crate::leanh::lean_inc(v_a_2160_);
                    v_a_2161_ = crate::leanh::lean_ctor_get(v_x_2135_, 1);
                    crate::leanh::lean_inc_ref(v_a_2161_);
                    crate::leanh::lean_dec_ref_known(v_x_2135_, 2);
                    crate::leanh::lean_inc(v_f_2134_);
                    v___f_2162_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_mapM___redArg___lam__2 as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_2162_, 0, v_toPure_2159_);
                    crate::leanh::lean_closure_set(v___f_2162_, 1, v_inst_2133_);
                    crate::leanh::lean_closure_set(v___f_2162_, 2, v_f_2134_);
                    crate::leanh::lean_closure_set(v___f_2162_, 3, v_a_2161_);
                    crate::leanh::lean_closure_set(v___f_2162_, 4, v_toBind_2158_);
                    v___x_2163_ = crate::leanh::lean_apply_1(v_f_2134_, v_a_2160_);
                    v___x_2164_ = crate::leanh::lean_apply_4(
                        v_toBind_2158_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
                    v_reuseFailAlloc_2145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2138_);
                    v___x_2143_ = v_reuseFailAlloc_2145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2144_ = crate::leanh::lean_apply_2(
                    v_toPure_2137_,
                    crate::leanh::lean_box(0),
                    v___x_2143_,
                );
                return v___x_2144_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___redArg___lam__2(
    mut v_toPure_2165_: *mut crate::leanh::LeanObject,
    mut v_inst_2166_: *mut crate::leanh::LeanObject,
    mut v_f_2167_: *mut crate::leanh::LeanObject,
    mut v_a_2168_: *mut crate::leanh::LeanObject,
    mut v_toBind_2169_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2171_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_TaggedText_mapM___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2171_, 0, v_____do__lift_2170_);
    crate::leanh::lean_closure_set(v___f_2171_, 1, v_toPure_2165_);
    v___x_2172_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_2166_, v_f_2167_, v_a_2168_);
    v___x_2173_ = crate::leanh::lean_apply_4(
        v_toBind_2169_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2172_,
        v___f_2171_,
    );
    return v___x_2173_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM(
    mut v_m_2174_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2175_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2176_: *mut crate::leanh::LeanObject,
    mut v_inst_2177_: *mut crate::leanh::LeanObject,
    mut v_f_2178_: *mut crate::leanh::LeanObject,
    mut v_x_2179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_2177_, v_f_2178_, v_x_2179_);
    return v___x_2180_;
}
pub unsafe fn l_Lean_Widget_TaggedText_forM___redArg___lam__1(
    mut v_inst_2181_: *mut crate::leanh::LeanObject,
    mut v_f_2182_: *mut crate::leanh::LeanObject,
    mut v_a_2183_: *mut crate::leanh::LeanObject,
    mut v_____r_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2185_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_2181_, v_f_2182_, v_a_2183_);
    return v___x_2185_;
}
pub unsafe fn l_Lean_Widget_TaggedText_forM___redArg(
    mut v_inst_2186_: *mut crate::leanh::LeanObject,
    mut v_f_2187_: *mut crate::leanh::LeanObject,
    mut v_x_2188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2188_) {
        0 => {
            let mut v_toApplicative_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_2189_ = crate::leanh::lean_ctor_get(v_inst_2186_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_2189_);
            crate::leanh::lean_dec_ref_known(v_x_2188_, 1);
            crate::leanh::lean_dec(v_f_2187_);
            crate::leanh::lean_dec_ref(v_inst_2186_);
            v_toPure_2190_ = crate::leanh::lean_ctor_get(v_toApplicative_2189_, 1);
            crate::leanh::lean_inc(v_toPure_2190_);
            crate::leanh::lean_dec_ref(v_toApplicative_2189_);
            v___x_2191_ = crate::leanh::lean_box(0);
            v___x_2192_ =
                crate::leanh::lean_apply_2(v_toPure_2190_, crate::leanh::lean_box(0), v___x_2191_);
            return v___x_2192_;
        }
        1 => {
            let mut v_toApplicative_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2199_: u8 = 0;
            v_toApplicative_2193_ = crate::leanh::lean_ctor_get(v_inst_2186_, 0);
            v_toPure_2194_ = crate::leanh::lean_ctor_get(v_toApplicative_2193_, 1);
            v_a_2195_ = crate::leanh::lean_ctor_get(v_x_2188_, 0);
            crate::leanh::lean_inc_ref(v_a_2195_);
            crate::leanh::lean_dec_ref_known(v_x_2188_, 1);
            v___x_2196_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_2197_ = lean_array_get_size(v_a_2195_);
            v___x_2198_ = crate::leanh::lean_box(0);
            v___x_2199_ = lean_nat_dec_lt(v___x_2196_, v___x_2197_);
            if v___x_2199_ == 0 {
                let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_toPure_2194_);
                crate::leanh::lean_dec_ref(v_a_2195_);
                crate::leanh::lean_dec(v_f_2187_);
                crate::leanh::lean_dec_ref(v_inst_2186_);
                v___x_2200_ = crate::leanh::lean_apply_2(
                    v_toPure_2194_,
                    crate::leanh::lean_box(0),
                    v___x_2198_,
                );
                return v___x_2200_;
            } else {
                let mut v___f_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2202_: u8 = 0;
                crate::leanh::lean_inc_ref(v_inst_2186_);
                v___f_2201_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Widget_TaggedText_forM___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2201_, 0, v_inst_2186_);
                crate::leanh::lean_closure_set(v___f_2201_, 1, v_f_2187_);
                v___x_2202_ = lean_nat_dec_le(v___x_2197_, v___x_2197_);
                if v___x_2202_ == 0 {
                    if v___x_2199_ == 0 {
                        let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_inc(v_toPure_2194_);
                        crate::leanh::lean_dec_ref(v___f_2201_);
                        crate::leanh::lean_dec_ref(v_a_2195_);
                        crate::leanh::lean_dec_ref(v_inst_2186_);
                        v___x_2203_ = crate::leanh::lean_apply_2(
                            v_toPure_2194_,
                            crate::leanh::lean_box(0),
                            v___x_2198_,
                        );
                        return v___x_2203_;
                    } else {
                        let mut v___x_2204_: usize = 0;
                        let mut v___x_2205_: usize = 0;
                        let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2204_ = 0usize;
                        v___x_2205_ = lean_usize_of_nat(v___x_2197_);
                        v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
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
                    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2207_ = 0usize;
                    v___x_2208_ = lean_usize_of_nat(v___x_2197_);
                    v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
            let mut v_toBind_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_2210_ = crate::leanh::lean_ctor_get(v_inst_2186_, 1);
            crate::leanh::lean_inc(v_toBind_2210_);
            v_a_2211_ = crate::leanh::lean_ctor_get(v_x_2188_, 0);
            crate::leanh::lean_inc(v_a_2211_);
            v_a_2212_ = crate::leanh::lean_ctor_get(v_x_2188_, 1);
            crate::leanh::lean_inc_ref_n(v_a_2212_, 2);
            crate::leanh::lean_dec_ref_known(v_x_2188_, 2);
            crate::leanh::lean_inc(v_f_2187_);
            v___f_2213_ = crate::leanh::lean_alloc_closure(
                l_Lean_Widget_TaggedText_forM___redArg___lam__1 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_2213_, 0, v_inst_2186_);
            crate::leanh::lean_closure_set(v___f_2213_, 1, v_f_2187_);
            crate::leanh::lean_closure_set(v___f_2213_, 2, v_a_2212_);
            v___x_2214_ = crate::leanh::lean_apply_2(v_f_2187_, v_a_2211_, v_a_2212_);
            v___x_2215_ = crate::leanh::lean_apply_4(
                v_toBind_2210_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2214_,
                v___f_2213_,
            );
            return v___x_2215_;
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_forM___redArg___lam__0(
    mut v_inst_2216_: *mut crate::leanh::LeanObject,
    mut v_f_2217_: *mut crate::leanh::LeanObject,
    mut v_x_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2220_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_2216_, v_f_2217_, v___y_2219_);
    return v___x_2220_;
}
pub unsafe fn l_Lean_Widget_TaggedText_forM(
    mut v_m_2221_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2222_: *mut crate::leanh::LeanObject,
    mut v_inst_2223_: *mut crate::leanh::LeanObject,
    mut v_f_2224_: *mut crate::leanh::LeanObject,
    mut v_x_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2226_ = l_Lean_Widget_TaggedText_forM___redArg(v_inst_2223_, v_f_2224_, v_x_2225_);
    return v___x_2226_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(
    mut v_f_2227_: *mut crate::leanh::LeanObject,
    mut v_sz_2228_: usize,
    mut v_i_2229_: usize,
    mut v_bs_2230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2231_: u8 = 0;
    let mut v_v_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: usize = 0;
    let mut v___x_2237_: usize = 0;
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2231_ = lean_usize_dec_lt(v_i_2229_, v_sz_2228_);
                if v___x_2231_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_2227_);
                    return v_bs_2230_;
                } else {
                    v_v_2232_ = lean_array_uget(v_bs_2230_, v_i_2229_);
                    v___x_2233_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2234_ = lean_array_uset(v_bs_2230_, v_i_2229_, v___x_2233_);
                    crate::leanh::lean_inc_ref(v_f_2227_);
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
    mut v_f_2240_: *mut crate::leanh::LeanObject,
    mut v_x_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_a_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2253_: u8 = 0;
    let mut v_sz_2254_: usize = 0;
    let mut v___x_2255_: usize = 0;
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v_a_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2241_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_f_2240_);
                    v_a_2242_ = crate::leanh::lean_ctor_get(v_x_2241_, 0);
                    v_isSharedCheck_2249_ = (!crate::leanh::lean_is_exclusive(v_x_2241_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v___x_2244_ = v_x_2241_;
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2242_);
                        crate::leanh::lean_dec(v_x_2241_);
                        v___x_2244_ = crate::leanh::lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_2250_ = crate::leanh::lean_ctor_get(v_x_2241_, 0);
                    v_isSharedCheck_2260_ = (!crate::leanh::lean_is_exclusive(v_x_2241_)) as u8;
                    if v_isSharedCheck_2260_ == 0 {
                        v___x_2252_ = v_x_2241_;
                        v_isShared_2253_ = v_isSharedCheck_2260_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2250_);
                        crate::leanh::lean_dec(v_x_2241_);
                        v___x_2252_ = crate::leanh::lean_box(0);
                        v_isShared_2253_ = v_isSharedCheck_2260_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_2261_ = crate::leanh::lean_ctor_get(v_x_2241_, 0);
                    crate::leanh::lean_inc(v_a_2261_);
                    v_a_2262_ = crate::leanh::lean_ctor_get(v_x_2241_, 1);
                    crate::leanh::lean_inc_ref(v_a_2262_);
                    crate::leanh::lean_dec_ref_known(v_x_2241_, 2);
                    v___x_2263_ = crate::leanh::lean_apply_2(v_f_2240_, v_a_2261_, v_a_2262_);
                    return v___x_2263_;
                }
            },
            1 => {
                if v_isShared_2245_ == 0 {
                    v___x_2247_ = v___x_2244_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
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
                    crate::leanh::lean_ctor_set(v___x_2252_, 0, v___x_2256_);
                    v___x_2258_ = v___x_2252_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
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
    mut v_f_2264_: *mut crate::leanh::LeanObject,
    mut v_sz_2265_: *mut crate::leanh::LeanObject,
    mut v_i_2266_: *mut crate::leanh::LeanObject,
    mut v_bs_2267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2268_: usize = 0;
    let mut v_i_boxed_2269_: usize = 0;
    let mut v_res_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2268_ = crate::leanh::lean_unbox_usize(v_sz_2265_);
    crate::leanh::lean_dec(v_sz_2265_);
    v_i_boxed_2269_ = crate::leanh::lean_unbox_usize(v_i_2266_);
    crate::leanh::lean_dec(v_i_2266_);
    v_res_2270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_2264_, v_sz_boxed_2268_, v_i_boxed_2269_, v_bs_2267_);
    return v_res_2270_;
}
pub unsafe fn l_Lean_Widget_TaggedText_rewrite(
    mut v_00_u03b1_2271_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2272_: *mut crate::leanh::LeanObject,
    mut v_f_2273_: *mut crate::leanh::LeanObject,
    mut v_x_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_Lean_Widget_TaggedText_rewrite___redArg(v_f_2273_, v_x_2274_);
    return v___x_2275_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(
    mut v_00_u03b1_2276_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2277_: *mut crate::leanh::LeanObject,
    mut v_f_2278_: *mut crate::leanh::LeanObject,
    mut v_sz_2279_: usize,
    mut v_i_2280_: usize,
    mut v_bs_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___redArg(v_f_2278_, v_sz_2279_, v_i_2280_, v_bs_2281_);
    return v___x_2282_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0___boxed(
    mut v_00_u03b1_2283_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2284_: *mut crate::leanh::LeanObject,
    mut v_f_2285_: *mut crate::leanh::LeanObject,
    mut v_sz_2286_: *mut crate::leanh::LeanObject,
    mut v_i_2287_: *mut crate::leanh::LeanObject,
    mut v_bs_2288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2289_: usize = 0;
    let mut v_i_boxed_2290_: usize = 0;
    let mut v_res_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2289_ = crate::leanh::lean_unbox_usize(v_sz_2286_);
    crate::leanh::lean_dec(v_sz_2286_);
    v_i_boxed_2290_ = crate::leanh::lean_unbox_usize(v_i_2287_);
    crate::leanh::lean_dec(v_i_2287_);
    v_res_2291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewrite_spec__0(v_00_u03b1_2283_, v_00_u03b2_2284_, v_f_2285_, v_sz_boxed_2289_, v_i_boxed_2290_, v_bs_2288_);
    return v_res_2291_;
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM___redArg(
    mut v_inst_2292_: *mut crate::leanh::LeanObject,
    mut v_f_2293_: *mut crate::leanh::LeanObject,
    mut v_x_2294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2305_: u8 = 0;
    let mut v_toApplicative_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2312_: usize = 0;
    let mut v___x_2313_: usize = 0;
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2294_) {
                0 => {
                    v_toApplicative_2295_ = crate::leanh::lean_ctor_get(v_inst_2292_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_2295_);
                    crate::leanh::lean_dec(v_f_2293_);
                    crate::leanh::lean_dec_ref(v_inst_2292_);
                    v_toPure_2296_ = crate::leanh::lean_ctor_get(v_toApplicative_2295_, 1);
                    crate::leanh::lean_inc(v_toPure_2296_);
                    crate::leanh::lean_dec_ref(v_toApplicative_2295_);
                    v_a_2297_ = crate::leanh::lean_ctor_get(v_x_2294_, 0);
                    v_isSharedCheck_2305_ = (!crate::leanh::lean_is_exclusive(v_x_2294_)) as u8;
                    if v_isSharedCheck_2305_ == 0 {
                        v___x_2299_ = v_x_2294_;
                        v_isShared_2300_ = v_isSharedCheck_2305_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2297_);
                        crate::leanh::lean_dec(v_x_2294_);
                        v___x_2299_ = crate::leanh::lean_box(0);
                        v_isShared_2300_ = v_isSharedCheck_2305_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_toApplicative_2306_ = crate::leanh::lean_ctor_get(v_inst_2292_, 0);
                    v_toBind_2307_ = crate::leanh::lean_ctor_get(v_inst_2292_, 1);
                    crate::leanh::lean_inc(v_toBind_2307_);
                    v_toPure_2308_ = crate::leanh::lean_ctor_get(v_toApplicative_2306_, 1);
                    v_a_2309_ = crate::leanh::lean_ctor_get(v_x_2294_, 0);
                    crate::leanh::lean_inc_ref(v_a_2309_);
                    crate::leanh::lean_dec_ref_known(v_x_2294_, 1);
                    crate::leanh::lean_inc(v_toPure_2308_);
                    v___f_2310_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_mapM___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2310_, 0, v_toPure_2308_);
                    crate::leanh::lean_inc_ref(v_inst_2292_);
                    v___x_2311_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Widget_TaggedText_rewriteM___redArg as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_2311_, 0, v_inst_2292_);
                    crate::leanh::lean_closure_set(v___x_2311_, 1, v_f_2293_);
                    v_sz_2312_ = lean_array_size(v_a_2309_);
                    v___x_2313_ = 0usize;
                    v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_2292_,
                        v___x_2311_,
                        v_sz_2312_,
                        v___x_2313_,
                        v_a_2309_,
                    );
                    v___x_2315_ = crate::leanh::lean_apply_4(
                        v_toBind_2307_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_2314_,
                        v___f_2310_,
                    );
                    return v___x_2315_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_inst_2292_);
                    v_a_2316_ = crate::leanh::lean_ctor_get(v_x_2294_, 0);
                    crate::leanh::lean_inc(v_a_2316_);
                    v_a_2317_ = crate::leanh::lean_ctor_get(v_x_2294_, 1);
                    crate::leanh::lean_inc_ref(v_a_2317_);
                    crate::leanh::lean_dec_ref_known(v_x_2294_, 2);
                    v___x_2318_ = crate::leanh::lean_apply_2(v_f_2293_, v_a_2316_, v_a_2317_);
                    return v___x_2318_;
                }
            },
            1 => {
                if v_isShared_2300_ == 0 {
                    v___x_2302_ = v___x_2299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2304_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2297_);
                    v___x_2302_ = v_reuseFailAlloc_2304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2303_ = crate::leanh::lean_apply_2(
                    v_toPure_2296_,
                    crate::leanh::lean_box(0),
                    v___x_2302_,
                );
                return v___x_2303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM(
    mut v_m_2319_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2320_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2321_: *mut crate::leanh::LeanObject,
    mut v_inst_2322_: *mut crate::leanh::LeanObject,
    mut v_f_2323_: *mut crate::leanh::LeanObject,
    mut v_x_2324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2325_ = l_Lean_Widget_TaggedText_rewriteM___redArg(v_inst_2322_, v_f_2323_, v_x_2324_);
    return v___x_2325_;
}
pub unsafe fn l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0(
    mut v_inst_2326_: *mut crate::leanh::LeanObject,
    mut v___x_2327_: *mut crate::leanh::LeanObject,
    mut v___x_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rpcEncode_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641__overap_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2338_: u8 = 0;
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rpcEncode_2331_ = crate::leanh::lean_ctor_get(v_inst_2326_, 0);
                crate::leanh::lean_inc_ref(v_rpcEncode_2331_);
                crate::leanh::lean_dec_ref(v_inst_2326_);
                v___x_641__overap_2332_ = l_Lean_Widget_TaggedText_mapM___redArg(
                    v___x_2327_,
                    v_rpcEncode_2331_,
                    v_a_2329_,
                );
                v___x_2333_ = crate::leanh::lean_apply_1(v___x_641__overap_2332_, v___y_2330_);
                v_fst_2334_ = crate::leanh::lean_ctor_get(v___x_2333_, 0);
                v_snd_2335_ = crate::leanh::lean_ctor_get(v___x_2333_, 1);
                v_isSharedCheck_2343_ = (!crate::leanh::lean_is_exclusive(v___x_2333_)) as u8;
                if v_isSharedCheck_2343_ == 0 {
                    v___x_2337_ = v___x_2333_;
                    v_isShared_2338_ = v_isSharedCheck_2343_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2335_);
                    crate::leanh::lean_inc(v_fst_2334_);
                    crate::leanh::lean_dec(v___x_2333_);
                    v___x_2337_ = crate::leanh::lean_box(0);
                    v_isShared_2338_ = v_isSharedCheck_2343_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2339_ =
                    l_Lean_Widget_instToJsonTaggedText_toJson___redArg(v___x_2328_, v_fst_2334_);
                if v_isShared_2338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2337_, 0, v___x_2339_);
                    v___x_2341_ = v___x_2337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_snd_2335_);
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
    mut v___f_2344_: *mut crate::leanh::LeanObject,
    mut v_inst_2345_: *mut crate::leanh::LeanObject,
    mut v___x_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2353_: u8 = 0;
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut v_a_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rpcDecode_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654__overap_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2349_ =
                    l_Lean_Widget_instFromJsonTaggedText_fromJson___redArg(v___f_2344_, v_a_2347_);
                if crate::leanh::lean_obj_tag(v___x_2349_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_2346_);
                    crate::leanh::lean_dec_ref(v_inst_2345_);
                    v_a_2350_ = crate::leanh::lean_ctor_get(v___x_2349_, 0);
                    v_isSharedCheck_2357_ = (!crate::leanh::lean_is_exclusive(v___x_2349_)) as u8;
                    if v_isSharedCheck_2357_ == 0 {
                        v___x_2352_ = v___x_2349_;
                        v_isShared_2353_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2350_);
                        crate::leanh::lean_dec(v___x_2349_);
                        v___x_2352_ = crate::leanh::lean_box(0);
                        v_isShared_2353_ = v_isSharedCheck_2357_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2358_ = crate::leanh::lean_ctor_get(v___x_2349_, 0);
                    crate::leanh::lean_inc(v_a_2358_);
                    crate::leanh::lean_dec_ref_known(v___x_2349_, 1);
                    v_rpcDecode_2359_ = crate::leanh::lean_ctor_get(v_inst_2345_, 1);
                    crate::leanh::lean_inc_ref(v_rpcDecode_2359_);
                    crate::leanh::lean_dec_ref(v_inst_2345_);
                    v___x_654__overap_2360_ = l_Lean_Widget_TaggedText_mapM___redArg(
                        v___x_2346_,
                        v_rpcDecode_2359_,
                        v_a_2358_,
                    );
                    crate::leanh::lean_inc_ref(v___y_2348_);
                    v___x_2361_ = crate::leanh::lean_apply_1(v___x_654__overap_2360_, v___y_2348_);
                    return v___x_2361_;
                }
            }
            1 => {
                if v_isShared_2353_ == 0 {
                    v___x_2355_ = v___x_2352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
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
    mut v___f_2362_: *mut crate::leanh::LeanObject,
    mut v_inst_2363_: *mut crate::leanh::LeanObject,
    mut v___x_2364_: *mut crate::leanh::LeanObject,
    mut v_a_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2367_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1(
        v___f_2362_,
        v_inst_2363_,
        v___x_2364_,
        v_a_2365_,
        v___y_2366_,
    );
    crate::leanh::lean_dec_ref(v___y_2366_);
    return v_res_2367_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__9;
    v___x_2415_ = l_ReaderT_instMonad___redArg(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___f_2417_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2417_, 0, v___x_2416_);
    return v___f_2417_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___f_2419_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2419_, 0, v___x_2418_);
    return v___f_2419_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___f_2421_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2421_, 0, v___x_2420_);
    return v___f_2421_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2422_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___f_2423_ = crate::leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2423_, 0, v___x_2422_);
    return v___f_2423_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___x_2425_ = crate::leanh::lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___x_2425_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2425_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2425_, 2, v___x_2424_);
    return v___x_2425_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__22,
    );
    v___x_2427_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__26,
    );
    v___x_2428_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2428_, 0, v___x_2427_);
    crate::leanh::lean_ctor_set(v___x_2428_, 1, v___f_2426_);
    return v___x_2428_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___x_2430_ = crate::leanh::lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2430_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2430_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2430_, 2, v___x_2429_);
    return v___x_2430_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2431_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__25,
    );
    v___f_2432_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__24,
    );
    v___f_2433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__23,
    );
    v___x_2434_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__28,
    );
    v___x_2435_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__27,
    );
    v___x_2436_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2436_, 0, v___x_2435_);
    crate::leanh::lean_ctor_set(v___x_2436_, 1, v___x_2434_);
    crate::leanh::lean_ctor_set(v___x_2436_, 2, v___f_2433_);
    crate::leanh::lean_ctor_set(v___x_2436_, 3, v___f_2432_);
    crate::leanh::lean_ctor_set(v___x_2436_, 4, v___f_2431_);
    return v___x_2436_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__21,
    );
    v___x_2438_ = crate::leanh::lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    crate::leanh::lean_closure_set(v___x_2438_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2438_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2438_, 2, v___x_2437_);
    return v___x_2438_;
}
pub unsafe fn _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2439_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__30,
    );
    v___x_2440_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__29,
    );
    v___x_2441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2441_, 0, v___x_2440_);
    crate::leanh::lean_ctor_set(v___x_2441_, 1, v___x_2439_);
    return v___x_2441_;
}
pub unsafe fn l_Lean_Widget_TaggedText_instRpcEncodable___redArg(
    mut v_inst_2443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19;
    v___x_2445_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__20;
    crate::leanh::lean_inc_ref(v_inst_2443_);
    v___f_2446_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2446_, 0, v_inst_2443_);
    crate::leanh::lean_closure_set(v___f_2446_, 1, v___x_2444_);
    crate::leanh::lean_closure_set(v___f_2446_, 2, v___x_2445_);
    v___x_2447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31_once
        ),
        _init_l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__31,
    );
    v___f_2448_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__32;
    v___f_2449_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_TaggedText_instRpcEncodable___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2449_, 0, v___f_2448_);
    crate::leanh::lean_closure_set(v___f_2449_, 1, v_inst_2443_);
    crate::leanh::lean_closure_set(v___f_2449_, 2, v___x_2447_);
    v___x_2450_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___f_2446_);
    crate::leanh::lean_ctor_set(v___x_2450_, 1, v___f_2449_);
    return v___x_2450_;
}
pub unsafe fn l_Lean_Widget_TaggedText_instRpcEncodable(
    mut v_00_u03b1_2451_: *mut crate::leanh::LeanObject,
    mut v_inst_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg(v_inst_2452_);
    return v___x_2453_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__0(
    mut v_s_2462_: *mut crate::leanh::LeanObject,
    mut v___y_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_out_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2464_ = crate::leanh::lean_ctor_get(v___y_2463_, 0);
                v_tagStack_2465_ = crate::leanh::lean_ctor_get(v___y_2463_, 1);
                v_column_2466_ = crate::leanh::lean_ctor_get(v___y_2463_, 2);
                v_isSharedCheck_2478_ = (!crate::leanh::lean_is_exclusive(v___y_2463_)) as u8;
                if v_isSharedCheck_2478_ == 0 {
                    v___x_2468_ = v___y_2463_;
                    v_isShared_2469_ = v_isSharedCheck_2478_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_2466_);
                    crate::leanh::lean_inc(v_tagStack_2465_);
                    crate::leanh::lean_inc(v_out_2464_);
                    crate::leanh::lean_dec(v___y_2463_);
                    v___x_2468_ = crate::leanh::lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2478_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2470_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_s_2462_);
                v___x_2471_ = l_Lean_Widget_TaggedText_appendText___redArg(v_s_2462_, v_out_2464_);
                v___x_2472_ = lean_string_length(v_s_2462_);
                crate::leanh::lean_dec_ref(v_s_2462_);
                v___x_2473_ = lean_nat_add(v_column_2466_, v___x_2472_);
                crate::leanh::lean_dec(v_column_2466_);
                if v_isShared_2469_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2468_, 2, v___x_2473_);
                    crate::leanh::lean_ctor_set(v___x_2468_, 0, v___x_2471_);
                    v___x_2475_ = v___x_2468_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2477_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_tagStack_2465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 2, v___x_2473_);
                    v___x_2475_ = v_reuseFailAlloc_2477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2476_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2476_, 0, v___x_2470_);
                crate::leanh::lean_ctor_set(v___x_2476_, 1, v___x_2475_);
                return v___x_2476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(
    mut v___x_2479_: u32,
    mut v_s_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = lean_string_push(v_s_2480_, v___x_2479_);
    return v___x_2481_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed(
    mut v___x_2482_: *mut crate::leanh::LeanObject,
    mut v_s_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_827__boxed_2484_: u32 = 0;
    let mut v_res_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_827__boxed_2484_ = crate::leanh::lean_unbox_uint32(v___x_2482_);
    crate::leanh::lean_dec(v___x_2482_);
    v_res_2485_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1(v___x_827__boxed_2484_, v_s_2483_);
    return v_res_2485_;
}
pub unsafe fn _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2487_: u32 = 0;
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2487_ = 32;
    v___x_2488_ = crate::leanh::lean_box_uint32(v___x_2487_);
    return v___x_2488_;
}
pub unsafe fn _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1;
    v___f_2490_ = crate::leanh::lean_alloc_closure(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_2490_, 0, v___x_2489_);
    return v___f_2490_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2(
    mut v_indent_2491_: *mut crate::leanh::LeanObject,
    mut v___y_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_out_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut v_unused_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2493_ = crate::leanh::lean_ctor_get(v___y_2492_, 0);
                v_tagStack_2494_ = crate::leanh::lean_ctor_get(v___y_2492_, 1);
                v_isSharedCheck_2507_ = (!crate::leanh::lean_is_exclusive(v___y_2492_)) as u8;
                if v_isSharedCheck_2507_ == 0 {
                    v_unused_2508_ = crate::leanh::lean_ctor_get(v___y_2492_, 2);
                    crate::leanh::lean_dec(v_unused_2508_);
                    v___x_2496_ = v___y_2492_;
                    v_isShared_2497_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tagStack_2494_);
                    crate::leanh::lean_inc(v_out_2493_);
                    crate::leanh::lean_dec(v___y_2492_);
                    v___x_2496_ = crate::leanh::lean_box(0);
                    v_isShared_2497_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2498_ = crate::leanh::lean_box(0);
                v___x_2499_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                v___f_2500_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1_once), _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1);
                crate::leanh::lean_inc(v_indent_2491_);
                v___x_2501_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(
                    crate::leanh::lean_box(0),
                    v___f_2500_,
                    v_indent_2491_,
                    v___x_2499_,
                );
                v___x_2502_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2501_, v_out_2493_);
                if v_isShared_2497_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2496_, 2, v_indent_2491_);
                    crate::leanh::lean_ctor_set(v___x_2496_, 0, v___x_2502_);
                    v___x_2504_ = v___x_2496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2506_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_tagStack_2494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 2, v_indent_2491_);
                    v___x_2504_ = v_reuseFailAlloc_2506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2505_, 0, v___x_2498_);
                crate::leanh::lean_ctor_set(v___x_2505_, 1, v___x_2504_);
                return v___x_2505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(
    mut v_____do__lift_2509_: *mut crate::leanh::LeanObject,
    mut v___y_2510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_column_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_column_2511_ = crate::leanh::lean_ctor_get(v_____do__lift_2509_, 2);
    crate::leanh::lean_inc(v_column_2511_);
    v___x_2512_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2512_, 0, v_column_2511_);
    crate::leanh::lean_ctor_set(v___x_2512_, 1, v___y_2510_);
    return v___x_2512_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3___boxed(
    mut v_____do__lift_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__3(v_____do__lift_2513_, v___y_2514_);
    crate::leanh::lean_dec_ref(v_____do__lift_2513_);
    return v_res_2515_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__4(
    mut v_n_2516_: *mut crate::leanh::LeanObject,
    mut v___y_2517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_out_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2523_: u8 = 0;
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2518_ = crate::leanh::lean_ctor_get(v___y_2517_, 0);
                v_tagStack_2519_ = crate::leanh::lean_ctor_get(v___y_2517_, 1);
                v_column_2520_ = crate::leanh::lean_ctor_get(v___y_2517_, 2);
                v_isSharedCheck_2533_ = (!crate::leanh::lean_is_exclusive(v___y_2517_)) as u8;
                if v_isSharedCheck_2533_ == 0 {
                    v___x_2522_ = v___y_2517_;
                    v_isShared_2523_ = v_isSharedCheck_2533_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_2520_);
                    crate::leanh::lean_inc(v_tagStack_2519_);
                    crate::leanh::lean_inc(v_out_2518_);
                    crate::leanh::lean_dec(v___y_2517_);
                    v___x_2522_ = crate::leanh::lean_box(0);
                    v_isShared_2523_ = v_isSharedCheck_2533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2524_ = crate::leanh::lean_box(0);
                v___x_2525_ = l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__0;
                crate::leanh::lean_inc(v_column_2520_);
                v___x_2526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2526_, 0, v_column_2520_);
                crate::leanh::lean_ctor_set(v___x_2526_, 1, v_out_2518_);
                v___x_2527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2527_, 0, v_n_2516_);
                crate::leanh::lean_ctor_set(v___x_2527_, 1, v___x_2526_);
                v___x_2528_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2528_, 0, v___x_2527_);
                crate::leanh::lean_ctor_set(v___x_2528_, 1, v_tagStack_2519_);
                if v_isShared_2523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2522_, 1, v___x_2528_);
                    crate::leanh::lean_ctor_set(v___x_2522_, 0, v___x_2525_);
                    v___x_2530_ = v___x_2522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_column_2520_);
                    v___x_2530_ = v_reuseFailAlloc_2532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2531_, 0, v___x_2524_);
                crate::leanh::lean_ctor_set(v___x_2531_, 1, v___x_2530_);
                return v___x_2531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__5(
    mut v_acc_2534_: *mut crate::leanh::LeanObject,
    mut v_x_2535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2536_ = crate::leanh::lean_ctor_get(v_x_2535_, 1);
                crate::leanh::lean_inc(v_snd_2536_);
                v_fst_2537_ = crate::leanh::lean_ctor_get(v_x_2535_, 0);
                crate::leanh::lean_inc(v_fst_2537_);
                crate::leanh::lean_dec_ref(v_x_2535_);
                v_fst_2538_ = crate::leanh::lean_ctor_get(v_snd_2536_, 0);
                v_snd_2539_ = crate::leanh::lean_ctor_get(v_snd_2536_, 1);
                v_isSharedCheck_2547_ = (!crate::leanh::lean_is_exclusive(v_snd_2536_)) as u8;
                if v_isSharedCheck_2547_ == 0 {
                    v___x_2541_ = v_snd_2536_;
                    v_isShared_2542_ = v_isSharedCheck_2547_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2539_);
                    crate::leanh::lean_inc(v_fst_2538_);
                    crate::leanh::lean_dec(v_snd_2536_);
                    v___x_2541_ = crate::leanh::lean_box(0);
                    v_isShared_2542_ = v_isSharedCheck_2547_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2542_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2541_, 1, v_fst_2538_);
                    crate::leanh::lean_ctor_set(v___x_2541_, 0, v_fst_2537_);
                    v___x_2544_ = v___x_2541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2546_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_fst_2537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_fst_2538_);
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
    mut v___f_2550_: *mut crate::leanh::LeanObject,
    mut v_n_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_out_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2553_ = crate::leanh::lean_ctor_get(v___y_2552_, 0);
                v_tagStack_2554_ = crate::leanh::lean_ctor_get(v___y_2552_, 1);
                v_column_2555_ = crate::leanh::lean_ctor_get(v___y_2552_, 2);
                v_isSharedCheck_2568_ = (!crate::leanh::lean_is_exclusive(v___y_2552_)) as u8;
                if v_isSharedCheck_2568_ == 0 {
                    v___x_2557_ = v___y_2552_;
                    v_isShared_2558_ = v_isSharedCheck_2568_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_2555_);
                    crate::leanh::lean_inc(v_tagStack_2554_);
                    crate::leanh::lean_inc(v_out_2553_);
                    crate::leanh::lean_dec(v___y_2552_);
                    v___x_2557_ = crate::leanh::lean_box(0);
                    v_isShared_2558_ = v_isSharedCheck_2568_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2559_ = crate::leanh::lean_box(0);
                v___x_2560_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                crate::leanh::lean_inc(v_n_2551_);
                crate::leanh::lean_inc(v_tagStack_2554_);
                v___x_2561_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_tagStack_2554_,
                    v_tagStack_2554_,
                    v_n_2551_,
                    v___x_2560_,
                );
                v___x_2562_ = l_List_drop___redArg(v_n_2551_, v_tagStack_2554_);
                crate::leanh::lean_dec(v_tagStack_2554_);
                v_out_x27_2563_ = l_List_foldl___redArg(v___f_2550_, v_out_2553_, v___x_2561_);
                if v_isShared_2558_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2557_, 1, v___x_2562_);
                    crate::leanh::lean_ctor_set(v___x_2557_, 0, v_out_x27_2563_);
                    v___x_2565_ = v___x_2557_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_out_x27_2563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___x_2562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_column_2555_);
                    v___x_2565_ = v_reuseFailAlloc_2567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2566_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2566_, 0, v___x_2559_);
                crate::leanh::lean_ctor_set(v___x_2566_, 1, v___x_2565_);
                return v___x_2566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(
    mut v_x_2589_: *mut crate::leanh::LeanObject,
    mut v_x_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2592_: u8 = 0;
    let mut v___x_2593_: u32 = 0;
    let mut v_one_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2591_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2592_ = lean_nat_dec_eq(v_x_2589_, v_zero_2591_);
                if v_isZero_2592_ == 1 {
                    crate::leanh::lean_dec(v_x_2589_);
                    return v_x_2590_;
                } else {
                    v___x_2593_ = 32;
                    v_one_2594_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2595_ = lean_nat_sub(v_x_2589_, v_one_2594_);
                    crate::leanh::lean_dec(v_x_2589_);
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
    mut v_fla_2598_: *mut crate::leanh::LeanObject,
    mut v_flb_2599_: u8,
    mut v_tail_2600_: *mut crate::leanh::LeanObject,
    mut v_is_x27_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2602_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2602_, 0, v_fla_2598_);
    crate::leanh::lean_ctor_set(v___x_2602_, 1, v_is_x27_2601_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2602_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_flb_2599_,
    );
    v___x_2603_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2603_, 0, v___x_2602_);
    crate::leanh::lean_ctor_set(v___x_2603_, 1, v_tail_2600_);
    return v___x_2603_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0___boxed(
    mut v_fla_2604_: *mut crate::leanh::LeanObject,
    mut v_flb_2605_: *mut crate::leanh::LeanObject,
    mut v_tail_2606_: *mut crate::leanh::LeanObject,
    mut v_is_x27_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flb_6181__boxed_2608_: u8 = 0;
    let mut v_res_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flb_6181__boxed_2608_ = (crate::leanh::lean_unbox(v_flb_2605_) as u8);
    v_res_2609_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2604_, v_flb_6181__boxed_2608_, v_tail_2606_, v_is_x27_2607_);
    return v_res_2609_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(
    mut v_flb_2610_: u8,
    mut v_items_2611_: *mut crate::leanh::LeanObject,
    mut v_gs_2612_: *mut crate::leanh::LeanObject,
    mut v_w_2613_: *mut crate::leanh::LeanObject,
    mut v___y_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2616_: u8 = 0;
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: u8 = 0;
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundFlattenedHardLine_2632_: u8 = 0;
    let mut v_space_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: u8 = 0;
    let mut v___x_2635_: u8 = 0;
    let mut v_foundLine_2636_: u8 = 0;
    let mut v_space_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2639_: u8 = 0;
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2642_: u8 = 0;
    let mut v_foundFlattenedHardLine_2643_: u8 = 0;
    let mut v_space_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v___x_2653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_column_2621_ = crate::leanh::lean_ctor_get(v___y_2614_, 2);
                v___x_2622_ = 0;
                v___x_2623_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_2610_, v___x_2622_);
                v___x_2624_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_2624_, 0 as u32, v___x_2623_);
                crate::leanh::lean_inc(v_items_2611_);
                v_g_2625_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v_g_2625_, 0, v___x_2624_);
                crate::leanh::lean_ctor_set(v_g_2625_, 1, v_items_2611_);
                crate::leanh::lean_ctor_set_uint8(
                    v_g_2625_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_flb_2610_,
                );
                v___x_2626_ = crate::leanh::lean_box(0);
                v___x_2627_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2627_, 0, v_g_2625_);
                crate::leanh::lean_ctor_set(v___x_2627_, 1, v___x_2626_);
                v___x_2628_ = lean_nat_sub(v_w_2613_, v_column_2621_);
                crate::leanh::lean_inc(v___x_2628_);
                crate::leanh::lean_inc(v_column_2621_);
                v_r_2629_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                    v___x_2627_,
                    v_column_2621_,
                    v___x_2628_,
                );
                v_foundLine_2636_ = crate::leanh::lean_ctor_get_uint8(
                    v_r_2629_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_space_2637_ = crate::leanh::lean_ctor_get(v_r_2629_, 0);
                crate::leanh::lean_inc(v_space_2637_);
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
                v___x_2617_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_2617_, 0 as u32, v___y_2616_);
                v___x_2618_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2618_, 0, v___x_2617_);
                crate::leanh::lean_ctor_set(v___x_2618_, 1, v_items_2611_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2618_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_flb_2610_,
                );
                v___x_2619_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2619_, 0, v___x_2618_);
                crate::leanh::lean_ctor_set(v___x_2619_, 1, v_gs_2612_);
                v___x_2620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2620_, 0, v___x_2619_);
                crate::leanh::lean_ctor_set(v___x_2620_, 1, v___y_2614_);
                return v___x_2620_;
            }
            2 => {
                v_foundFlattenedHardLine_2632_ = crate::leanh::lean_ctor_get_uint8(
                    v_r_2629_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_r_2629_);
                if v_foundFlattenedHardLine_2632_ == 0 {
                    v_space_2633_ = crate::leanh::lean_ctor_get(v___y_2631_, 0);
                    crate::leanh::lean_inc(v_space_2633_);
                    crate::leanh::lean_dec_ref(v___y_2631_);
                    v___x_2634_ = lean_nat_dec_le(v_space_2633_, v___x_2628_);
                    crate::leanh::lean_dec(v___x_2628_);
                    crate::leanh::lean_dec(v_space_2633_);
                    v___y_2616_ = v___x_2634_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2631_);
                    crate::leanh::lean_dec(v___x_2628_);
                    v___x_2635_ = 0;
                    v___y_2616_ = v___x_2635_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2639_ == 0 {
                    v___x_2640_ = lean_nat_sub(v___x_2628_, v_space_2637_);
                    crate::leanh::lean_inc(v_column_2621_);
                    crate::leanh::lean_inc(v_gs_2612_);
                    v_r_u2082_2641_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                            v_gs_2612_,
                            v_column_2621_,
                            v___x_2640_,
                        );
                    v_foundLine_2642_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_2641_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_2643_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_2641_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_2644_ = crate::leanh::lean_ctor_get(v_r_u2082_2641_, 0);
                    v_isSharedCheck_2652_ =
                        (!crate::leanh::lean_is_exclusive(v_r_u2082_2641_)) as u8;
                    if v_isSharedCheck_2652_ == 0 {
                        v___x_2646_ = v_r_u2082_2641_;
                        v_isShared_2647_ = v_isSharedCheck_2652_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_space_2644_);
                        crate::leanh::lean_dec(v_r_u2082_2641_);
                        v___x_2646_ = crate::leanh::lean_box(0);
                        v_isShared_2647_ = v_isSharedCheck_2652_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_space_2637_);
                    crate::leanh::lean_inc_ref(v_r_2629_);
                    v___y_2631_ = v_r_2629_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2648_ = lean_nat_add(v_space_2637_, v_space_2644_);
                crate::leanh::lean_dec(v_space_2644_);
                crate::leanh::lean_dec(v_space_2637_);
                if v_isShared_2647_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2646_, 0, v___x_2648_);
                    v___x_2650_ = v___x_2646_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2651_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_foundLine_2642_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2651_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
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
    mut v_flb_2654_: *mut crate::leanh::LeanObject,
    mut v_items_2655_: *mut crate::leanh::LeanObject,
    mut v_gs_2656_: *mut crate::leanh::LeanObject,
    mut v_w_2657_: *mut crate::leanh::LeanObject,
    mut v___y_2658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flb_boxed_2659_: u8 = 0;
    let mut v_res_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flb_boxed_2659_ = (crate::leanh::lean_unbox(v_flb_2654_) as u8);
    v_res_2660_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_boxed_2659_, v_items_2655_, v_gs_2656_, v_w_2657_, v___y_2658_);
    crate::leanh::lean_dec(v_w_2657_);
    return v_res_2660_;
}
pub unsafe fn l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(
    mut v_x_2661_: *mut crate::leanh::LeanObject,
    mut v_x_2662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2662_) == 0 {
                    return v_x_2661_;
                } else {
                    v_head_2663_ = crate::leanh::lean_ctor_get(v_x_2662_, 0);
                    crate::leanh::lean_inc(v_head_2663_);
                    v_snd_2664_ = crate::leanh::lean_ctor_get(v_head_2663_, 1);
                    crate::leanh::lean_inc(v_snd_2664_);
                    v_tail_2665_ = crate::leanh::lean_ctor_get(v_x_2662_, 1);
                    crate::leanh::lean_inc(v_tail_2665_);
                    crate::leanh::lean_dec_ref_known(v_x_2662_, 2);
                    v_fst_2666_ = crate::leanh::lean_ctor_get(v_head_2663_, 0);
                    crate::leanh::lean_inc(v_fst_2666_);
                    crate::leanh::lean_dec(v_head_2663_);
                    v_fst_2667_ = crate::leanh::lean_ctor_get(v_snd_2664_, 0);
                    v_snd_2668_ = crate::leanh::lean_ctor_get(v_snd_2664_, 1);
                    v_isSharedCheck_2677_ = (!crate::leanh::lean_is_exclusive(v_snd_2664_)) as u8;
                    if v_isSharedCheck_2677_ == 0 {
                        v___x_2670_ = v_snd_2664_;
                        v_isShared_2671_ = v_isSharedCheck_2677_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2668_);
                        crate::leanh::lean_inc(v_fst_2667_);
                        crate::leanh::lean_dec(v_snd_2664_);
                        v___x_2670_ = crate::leanh::lean_box(0);
                        v_isShared_2671_ = v_isSharedCheck_2677_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2671_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2670_, 1, v_fst_2667_);
                    crate::leanh::lean_ctor_set(v___x_2670_, 0, v_fst_2666_);
                    v___x_2673_ = v___x_2670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_fst_2666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_fst_2667_);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2678_ = crate::leanh::lean_box(0);
    v___x_2679_ = l_Lean_Widget_TaggedText_instRpcEncodable___redArg___closed__19;
    v___x_2680_ = l_instInhabitedOfMonad___redArg(v___x_2679_, v___x_2678_);
    return v___x_2680_;
}
pub unsafe fn l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(
    mut v_msg_2681_: *mut crate::leanh::LeanObject,
    mut v___y_2682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132__overap_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0_once), _init_l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5___closed__0);
    v___x_6132__overap_2684_ = lean_panic_fn_borrowed(v___x_2683_, v_msg_2681_);
    v___x_2685_ = crate::leanh::lean_apply_1(v___x_6132__overap_2684_, v___y_2682_);
    return v___x_2685_;
}
pub unsafe fn _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2687_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0;
    v___x_2688_ = lean_string_length(v___x_2687_);
    return v___x_2688_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(
    mut v_w_2690_: *mut crate::leanh::LeanObject,
    mut v_x_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2703_: u8 = 0;
    let mut v_fla_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flb_2705_: u8 = 0;
    let mut v_tail_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v_f_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeTags_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v_out_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: u8 = 0;
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u32 = 0;
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2755_: u8 = 0;
    let mut v___y_2757_: u8 = 0;
    let mut v_out_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2763_: u8 = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2773_: u8 = 0;
    let mut v_out_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2789_: u8 = 0;
    let mut v___x_2790_: u8 = 0;
    let mut v_out_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2809_: u8 = 0;
    let mut v_unused_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    let mut v_out_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v_unused_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fla_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: u8 = 0;
    let mut v_out_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2867_: u8 = 0;
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2882_: u8 = 0;
    let mut v_unused_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v_snd_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_force_2905_: u8 = 0;
    let mut v___x_2906_: u8 = 0;
    let mut v_a_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2910_: u8 = 0;
    let mut v___x_2911_: u32 = 0;
    let mut v_p_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: u8 = 0;
    let mut v_out_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2919_: u8 = 0;
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_is_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2949_: u8 = 0;
    let mut v_unused_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2956_: u8 = 0;
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_x27_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2969_: u8 = 0;
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_indent_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_behavior_2998_: u8 = 0;
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tagStack_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_unused_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v_unused_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2691_) == 0 {
                    v___x_2693_ = crate::leanh::lean_box(0);
                    v___x_2694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2694_, 0, v___x_2693_);
                    crate::leanh::lean_ctor_set(v___x_2694_, 1, v___y_2692_);
                    return v___x_2694_;
                } else {
                    v_head_2695_ = crate::leanh::lean_ctor_get(v_x_2691_, 0);
                    v_items_2696_ = crate::leanh::lean_ctor_get(v_head_2695_, 1);
                    crate::leanh::lean_inc(v_items_2696_);
                    if crate::leanh::lean_obj_tag(v_items_2696_) == 0 {
                        v_tail_2697_ = crate::leanh::lean_ctor_get(v_x_2691_, 1);
                        crate::leanh::lean_inc(v_tail_2697_);
                        crate::leanh::lean_dec_ref_known(v_x_2691_, 2);
                        v_x_2691_ = v_tail_2697_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_head_2695_);
                        v_head_2699_ = crate::leanh::lean_ctor_get(v_items_2696_, 0);
                        crate::leanh::lean_inc(v_head_2699_);
                        v_tail_2700_ = crate::leanh::lean_ctor_get(v_x_2691_, 1);
                        v_isSharedCheck_3051_ = (!crate::leanh::lean_is_exclusive(v_x_2691_)) as u8;
                        if v_isSharedCheck_3051_ == 0 {
                            v_unused_3052_ = crate::leanh::lean_ctor_get(v_x_2691_, 0);
                            crate::leanh::lean_dec(v_unused_3052_);
                            v___x_2702_ = v_x_2691_;
                            v_isShared_2703_ = v_isSharedCheck_3051_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_2700_);
                            crate::leanh::lean_dec(v_x_2691_);
                            v___x_2702_ = crate::leanh::lean_box(0);
                            v_isShared_2703_ = v_isSharedCheck_3051_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fla_2704_ = crate::leanh::lean_ctor_get(v_head_2695_, 0);
                crate::leanh::lean_inc(v_fla_2704_);
                v_flb_2705_ = crate::leanh::lean_ctor_get_uint8(
                    v_head_2695_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                crate::leanh::lean_dec(v_head_2695_);
                v_tail_2706_ = crate::leanh::lean_ctor_get(v_items_2696_, 1);
                v_isSharedCheck_3049_ = (!crate::leanh::lean_is_exclusive(v_items_2696_)) as u8;
                if v_isSharedCheck_3049_ == 0 {
                    v_unused_3050_ = crate::leanh::lean_ctor_get(v_items_2696_, 0);
                    crate::leanh::lean_dec(v_unused_3050_);
                    v___x_2708_ = v_items_2696_;
                    v_isShared_2709_ = v_isSharedCheck_3049_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tail_2706_);
                    crate::leanh::lean_dec(v_items_2696_);
                    v___x_2708_ = crate::leanh::lean_box(0);
                    v_isShared_2709_ = v_isSharedCheck_3049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_f_2710_ = crate::leanh::lean_ctor_get(v_head_2699_, 0);
                v_indent_2711_ = crate::leanh::lean_ctor_get(v_head_2699_, 1);
                v_activeTags_2712_ = crate::leanh::lean_ctor_get(v_head_2699_, 2);
                v_isSharedCheck_3048_ = (!crate::leanh::lean_is_exclusive(v_head_2699_)) as u8;
                if v_isSharedCheck_3048_ == 0 {
                    v___x_2714_ = v_head_2699_;
                    v_isShared_2715_ = v_isSharedCheck_3048_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeTags_2712_);
                    crate::leanh::lean_inc(v_indent_2711_);
                    crate::leanh::lean_inc(v_f_2710_);
                    crate::leanh::lean_dec(v_head_2699_);
                    v___x_2714_ = crate::leanh::lean_box(0);
                    v_isShared_2715_ = v_isSharedCheck_3048_;
                    state = 3;
                    continue;
                }
            }
            3 => match crate::leanh::lean_obj_tag(v_f_2710_) {
                0 => {
                    crate::leanh::lean_del_object(v___x_2714_);
                    crate::leanh::lean_dec(v_indent_2711_);
                    crate::leanh::lean_del_object(v___x_2708_);
                    crate::leanh::lean_del_object(v___x_2702_);
                    v_out_2774_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_2775_ = crate::leanh::lean_ctor_get(v___y_2692_, 1);
                    v_column_2776_ = crate::leanh::lean_ctor_get(v___y_2692_, 2);
                    v_isSharedCheck_2789_ = (!crate::leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_2789_ == 0 {
                        v___x_2778_ = v___y_2692_;
                        v_isShared_2779_ = v_isSharedCheck_2789_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_column_2776_);
                        crate::leanh::lean_inc(v_tagStack_2775_);
                        crate::leanh::lean_inc(v_out_2774_);
                        crate::leanh::lean_dec(v___y_2692_);
                        v___x_2778_ = crate::leanh::lean_box(0);
                        v_isShared_2779_ = v_isSharedCheck_2789_;
                        state = 11;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_2714_);
                    crate::leanh::lean_del_object(v___x_2708_);
                    crate::leanh::lean_del_object(v___x_2702_);
                    if v_flb_2705_ == 0 {
                        v___x_2790_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2704_);
                        if v___x_2790_ == 0 {
                            v_out_2791_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
                            v_tagStack_2792_ = crate::leanh::lean_ctor_get(v___y_2692_, 1);
                            v_isSharedCheck_2809_ =
                                (!crate::leanh::lean_is_exclusive(v___y_2692_)) as u8;
                            if v_isSharedCheck_2809_ == 0 {
                                v_unused_2810_ = crate::leanh::lean_ctor_get(v___y_2692_, 2);
                                crate::leanh::lean_dec(v_unused_2810_);
                                v___x_2794_ = v___y_2692_;
                                v_isShared_2795_ = v_isSharedCheck_2809_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_tagStack_2792_);
                                crate::leanh::lean_inc(v_out_2791_);
                                crate::leanh::lean_dec(v___y_2692_);
                                v___x_2794_ = crate::leanh::lean_box(0);
                                v_isShared_2795_ = v_isSharedCheck_2809_;
                                state = 13;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_indent_2711_);
                            v_out_2811_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
                            v_tagStack_2812_ = crate::leanh::lean_ctor_get(v___y_2692_, 1);
                            v_column_2813_ = crate::leanh::lean_ctor_get(v___y_2692_, 2);
                            v_isSharedCheck_2830_ =
                                (!crate::leanh::lean_is_exclusive(v___y_2692_)) as u8;
                            if v_isSharedCheck_2830_ == 0 {
                                v___x_2815_ = v___y_2692_;
                                v_isShared_2816_ = v_isSharedCheck_2830_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_column_2813_);
                                crate::leanh::lean_inc(v_tagStack_2812_);
                                crate::leanh::lean_inc(v_out_2811_);
                                crate::leanh::lean_dec(v___y_2692_);
                                v___x_2815_ = crate::leanh::lean_box(0);
                                v_isShared_2816_ = v_isSharedCheck_2830_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        v___x_2831_ = l_Int_toNat(v_indent_2711_);
                        crate::leanh::lean_dec(v_indent_2711_);
                        v___x_2832_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2704_);
                        crate::leanh::lean_dec(v_fla_2704_);
                        if v___x_2832_ == 0 {
                            v_out_2833_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
                            v_tagStack_2834_ = crate::leanh::lean_ctor_get(v___y_2692_, 1);
                            v_isSharedCheck_2852_ =
                                (!crate::leanh::lean_is_exclusive(v___y_2692_)) as u8;
                            if v_isSharedCheck_2852_ == 0 {
                                v_unused_2853_ = crate::leanh::lean_ctor_get(v___y_2692_, 2);
                                crate::leanh::lean_dec(v_unused_2853_);
                                v___x_2836_ = v___y_2692_;
                                v_isShared_2837_ = v_isSharedCheck_2852_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_tagStack_2834_);
                                crate::leanh::lean_inc(v_out_2833_);
                                crate::leanh::lean_dec(v___y_2692_);
                                v___x_2836_ = crate::leanh::lean_box(0);
                                v_isShared_2837_ = v_isSharedCheck_2852_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v___x_2854_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__0;
                            v___x_2855_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1_once), _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__1);
                            v___x_2856_ = lean_nat_sub(v_w_2690_, v___x_2855_);
                            crate::leanh::lean_inc(v_tail_2700_);
                            crate::leanh::lean_inc(v_tail_2706_);
                            v___x_2857_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_2705_, v_tail_2706_, v_tail_2700_, v___x_2856_, v___y_2692_);
                            crate::leanh::lean_dec(v___x_2856_);
                            v_fst_2858_ = crate::leanh::lean_ctor_get(v___x_2857_, 0);
                            crate::leanh::lean_inc(v_fst_2858_);
                            if crate::leanh::lean_obj_tag(v_fst_2858_) == 1 {
                                v_head_2859_ = crate::leanh::lean_ctor_get(v_fst_2858_, 0);
                                v_snd_2860_ = crate::leanh::lean_ctor_get(v___x_2857_, 1);
                                crate::leanh::lean_inc(v_snd_2860_);
                                crate::leanh::lean_dec_ref(v___x_2857_);
                                v_fla_2861_ = crate::leanh::lean_ctor_get(v_head_2859_, 0);
                                v___x_2862_ =
                                    l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2861_);
                                if v___x_2862_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v_fst_2858_, 2);
                                    v_out_2863_ = crate::leanh::lean_ctor_get(v_snd_2860_, 0);
                                    v_tagStack_2864_ = crate::leanh::lean_ctor_get(v_snd_2860_, 1);
                                    v_isSharedCheck_2882_ =
                                        (!crate::leanh::lean_is_exclusive(v_snd_2860_)) as u8;
                                    if v_isSharedCheck_2882_ == 0 {
                                        v_unused_2883_ =
                                            crate::leanh::lean_ctor_get(v_snd_2860_, 2);
                                        crate::leanh::lean_dec(v_unused_2883_);
                                        v___x_2866_ = v_snd_2860_;
                                        v_isShared_2867_ = v_isSharedCheck_2882_;
                                        state = 19;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_tagStack_2864_);
                                        crate::leanh::lean_inc(v_out_2863_);
                                        crate::leanh::lean_dec(v_snd_2860_);
                                        v___x_2866_ = crate::leanh::lean_box(0);
                                        v_isShared_2867_ = v_isSharedCheck_2882_;
                                        state = 19;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2831_);
                                    crate::leanh::lean_dec(v_tail_2706_);
                                    crate::leanh::lean_dec(v_tail_2700_);
                                    v_out_2884_ = crate::leanh::lean_ctor_get(v_snd_2860_, 0);
                                    v_tagStack_2885_ = crate::leanh::lean_ctor_get(v_snd_2860_, 1);
                                    v_column_2886_ = crate::leanh::lean_ctor_get(v_snd_2860_, 2);
                                    v_isSharedCheck_2901_ =
                                        (!crate::leanh::lean_is_exclusive(v_snd_2860_)) as u8;
                                    if v_isSharedCheck_2901_ == 0 {
                                        v___x_2888_ = v_snd_2860_;
                                        v_isShared_2889_ = v_isSharedCheck_2901_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_column_2886_);
                                        crate::leanh::lean_inc(v_tagStack_2885_);
                                        crate::leanh::lean_inc(v_out_2884_);
                                        crate::leanh::lean_dec(v_snd_2860_);
                                        v___x_2888_ = crate::leanh::lean_box(0);
                                        v_isShared_2889_ = v_isSharedCheck_2901_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_2858_);
                                crate::leanh::lean_dec(v___x_2831_);
                                crate::leanh::lean_dec(v_activeTags_2712_);
                                crate::leanh::lean_dec(v_tail_2706_);
                                crate::leanh::lean_dec(v_tail_2700_);
                                v_snd_2902_ = crate::leanh::lean_ctor_get(v___x_2857_, 1);
                                crate::leanh::lean_inc(v_snd_2902_);
                                crate::leanh::lean_dec_ref(v___x_2857_);
                                v___x_2903_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___closed__2;
                                v___x_2904_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__5(v___x_2903_, v_snd_2902_);
                                return v___x_2904_;
                            }
                        }
                    }
                }
                2 => {
                    crate::leanh::lean_del_object(v___x_2714_);
                    crate::leanh::lean_del_object(v___x_2708_);
                    crate::leanh::lean_del_object(v___x_2702_);
                    v_force_2905_ = crate::leanh::lean_ctor_get_uint8(v_f_2710_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_f_2710_, 0);
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
                    crate::leanh::lean_del_object(v___x_2702_);
                    v_a_2907_ = crate::leanh::lean_ctor_get(v_f_2710_, 0);
                    v_isSharedCheck_2970_ = (!crate::leanh::lean_is_exclusive(v_f_2710_)) as u8;
                    if v_isSharedCheck_2970_ == 0 {
                        v___x_2909_ = v_f_2710_;
                        v_isShared_2910_ = v_isSharedCheck_2970_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2907_);
                        crate::leanh::lean_dec(v_f_2710_);
                        v___x_2909_ = crate::leanh::lean_box(0);
                        v_isShared_2910_ = v_isSharedCheck_2970_;
                        state = 23;
                        continue;
                    }
                }
                4 => {
                    crate::leanh::lean_del_object(v___x_2702_);
                    v_indent_2971_ = crate::leanh::lean_ctor_get(v_f_2710_, 0);
                    crate::leanh::lean_inc(v_indent_2971_);
                    v_f_2972_ = crate::leanh::lean_ctor_get(v_f_2710_, 1);
                    crate::leanh::lean_inc(v_f_2972_);
                    crate::leanh::lean_dec_ref_known(v_f_2710_, 2);
                    v___x_2973_ = lean_int_add(v_indent_2711_, v_indent_2971_);
                    crate::leanh::lean_dec(v_indent_2971_);
                    crate::leanh::lean_dec(v_indent_2711_);
                    if v_isShared_2715_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2714_, 1, v___x_2973_);
                        crate::leanh::lean_ctor_set(v___x_2714_, 0, v_f_2972_);
                        v___x_2975_ = v___x_2714_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2981_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_f_2972_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2973_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_activeTags_2712_);
                        v___x_2975_ = v_reuseFailAlloc_2981_;
                        state = 31;
                        continue;
                    }
                }
                5 => {
                    v_a_2982_ = crate::leanh::lean_ctor_get(v_f_2710_, 0);
                    crate::leanh::lean_inc(v_a_2982_);
                    v_a_2983_ = crate::leanh::lean_ctor_get(v_f_2710_, 1);
                    crate::leanh::lean_inc(v_a_2983_);
                    crate::leanh::lean_dec_ref_known(v_f_2710_, 2);
                    v___x_2984_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v_indent_2711_);
                    if v_isShared_2715_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2714_, 2, v___x_2984_);
                        crate::leanh::lean_ctor_set(v___x_2714_, 0, v_a_2982_);
                        v___x_2986_ = v___x_2714_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_2996_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2982_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_indent_2711_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 2, v___x_2984_);
                        v___x_2986_ = v_reuseFailAlloc_2996_;
                        state = 33;
                        continue;
                    }
                }
                6 => {
                    crate::leanh::lean_del_object(v___x_2702_);
                    v_a_2997_ = crate::leanh::lean_ctor_get(v_f_2710_, 0);
                    crate::leanh::lean_inc(v_a_2997_);
                    v_behavior_2998_ = crate::leanh::lean_ctor_get_uint8(
                        v_f_2710_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_f_2710_, 1);
                    v___x_2999_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2704_);
                    if v___x_2999_ == 0 {
                        if v_isShared_2715_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2714_, 0, v_a_2997_);
                            v___x_3001_ = v___x_2714_;
                            state = 36;
                            continue;
                        } else {
                            v_reuseFailAlloc_3011_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_2997_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_indent_2711_);
                            crate::leanh::lean_ctor_set(
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
                            crate::leanh::lean_ctor_set(v___x_2714_, 0, v_a_2997_);
                            v___x_3013_ = v___x_2714_;
                            state = 38;
                            continue;
                        } else {
                            v_reuseFailAlloc_3019_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_2997_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_indent_2711_);
                            crate::leanh::lean_ctor_set(
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
                    v_a_3020_ = crate::leanh::lean_ctor_get(v_f_2710_, 0);
                    crate::leanh::lean_inc(v_a_3020_);
                    v_a_3021_ = crate::leanh::lean_ctor_get(v_f_2710_, 1);
                    crate::leanh::lean_inc(v_a_3021_);
                    crate::leanh::lean_dec_ref_known(v_f_2710_, 2);
                    v_out_3022_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_3023_ = crate::leanh::lean_ctor_get(v___y_2692_, 1);
                    v_column_3024_ = crate::leanh::lean_ctor_get(v___y_2692_, 2);
                    v_isSharedCheck_3047_ = (!crate::leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_3047_ == 0 {
                        v___x_3026_ = v___y_2692_;
                        v_isShared_3027_ = v_isSharedCheck_3047_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_column_3024_);
                        crate::leanh::lean_inc(v_tagStack_3023_);
                        crate::leanh::lean_inc(v_out_3022_);
                        crate::leanh::lean_dec(v___y_2692_);
                        v___x_3026_ = crate::leanh::lean_box(0);
                        v_isShared_3027_ = v_isSharedCheck_3047_;
                        state = 40;
                        continue;
                    }
                }
            },
            4 => {
                v_out_2717_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
                v_tagStack_2718_ = crate::leanh::lean_ctor_get(v___y_2692_, 1);
                v_column_2719_ = crate::leanh::lean_ctor_get(v___y_2692_, 2);
                v_isSharedCheck_2755_ = (!crate::leanh::lean_is_exclusive(v___y_2692_)) as u8;
                if v_isSharedCheck_2755_ == 0 {
                    v___x_2721_ = v___y_2692_;
                    v_isShared_2722_ = v_isSharedCheck_2755_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_2719_);
                    crate::leanh::lean_inc(v_tagStack_2718_);
                    crate::leanh::lean_inc(v_out_2717_);
                    crate::leanh::lean_dec(v___y_2692_);
                    v___x_2721_ = crate::leanh::lean_box(0);
                    v_isShared_2722_ = v_isSharedCheck_2755_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_column_2719_);
                v___x_2723_ = lean_nat_to_int(v_column_2719_);
                v___x_2724_ = lean_int_dec_lt(v___x_2723_, v_indent_2711_);
                if v___x_2724_ == 0 {
                    crate::leanh::lean_dec(v___x_2723_);
                    crate::leanh::lean_dec(v_column_2719_);
                    v___x_2725_ = l_Int_toNat(v_indent_2711_);
                    crate::leanh::lean_dec(v_indent_2711_);
                    v___x_2726_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                    crate::leanh::lean_inc(v___x_2725_);
                    v___x_2727_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2725_, v___x_2726_);
                    v___x_2728_ =
                        l_Lean_Widget_TaggedText_appendText___redArg(v___x_2727_, v_out_2717_);
                    v___x_2729_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                    crate::leanh::lean_inc(v_activeTags_2712_);
                    crate::leanh::lean_inc(v_tagStack_2718_);
                    v___x_2730_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                        crate::leanh::lean_box(0),
                        v_tagStack_2718_,
                        v_tagStack_2718_,
                        v_activeTags_2712_,
                        v___x_2729_,
                    );
                    v___x_2731_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2718_);
                    crate::leanh::lean_dec(v_tagStack_2718_);
                    v_out_x27_2732_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2728_, v___x_2730_);
                    if v_isShared_2722_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2721_, 2, v___x_2725_);
                        crate::leanh::lean_ctor_set(v___x_2721_, 1, v___x_2731_);
                        crate::leanh::lean_ctor_set(v___x_2721_, 0, v_out_x27_2732_);
                        v___x_2734_ = v___x_2721_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2737_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_out_x27_2732_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 1, v___x_2731_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 2, v___x_2725_);
                        v___x_2734_ = v_reuseFailAlloc_2737_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_2738_ = l_Lean_Widget_instInhabitedTaggedText_default___closed__0;
                    v___x_2739_ = 32;
                    v___x_2740_ = lean_int_sub(v_indent_2711_, v___x_2723_);
                    crate::leanh::lean_dec(v___x_2723_);
                    crate::leanh::lean_dec(v_indent_2711_);
                    v___x_2741_ = l_Int_toNat(v___x_2740_);
                    crate::leanh::lean_dec(v___x_2740_);
                    v___x_2742_ = lean_string_pushn(v___x_2738_, v___x_2739_, v___x_2741_);
                    crate::leanh::lean_inc_ref(v___x_2742_);
                    v___x_2743_ =
                        l_Lean_Widget_TaggedText_appendText___redArg(v___x_2742_, v_out_2717_);
                    v___x_2744_ = lean_string_length(v___x_2742_);
                    crate::leanh::lean_dec_ref(v___x_2742_);
                    v___x_2745_ = lean_nat_add(v_column_2719_, v___x_2744_);
                    crate::leanh::lean_dec(v_column_2719_);
                    v___x_2746_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                    crate::leanh::lean_inc(v_activeTags_2712_);
                    crate::leanh::lean_inc(v_tagStack_2718_);
                    v___x_2747_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                        crate::leanh::lean_box(0),
                        v_tagStack_2718_,
                        v_tagStack_2718_,
                        v_activeTags_2712_,
                        v___x_2746_,
                    );
                    v___x_2748_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2718_);
                    crate::leanh::lean_dec(v_tagStack_2718_);
                    v_out_x27_2749_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2743_, v___x_2747_);
                    if v_isShared_2722_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2721_, 2, v___x_2745_);
                        crate::leanh::lean_ctor_set(v___x_2721_, 1, v___x_2748_);
                        crate::leanh::lean_ctor_set(v___x_2721_, 0, v_out_x27_2749_);
                        v___x_2751_ = v___x_2721_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2754_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_out_x27_2749_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 1, v___x_2748_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 2, v___x_2745_);
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
                    crate::leanh::lean_dec(v_indent_2711_);
                    v_out_2758_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_2759_ = crate::leanh::lean_ctor_get(v___y_2692_, 1);
                    v_column_2760_ = crate::leanh::lean_ctor_get(v___y_2692_, 2);
                    v_isSharedCheck_2773_ = (!crate::leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_2773_ == 0 {
                        v___x_2762_ = v___y_2692_;
                        v_isShared_2763_ = v_isSharedCheck_2773_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_column_2760_);
                        crate::leanh::lean_inc(v_tagStack_2759_);
                        crate::leanh::lean_inc(v_out_2758_);
                        crate::leanh::lean_dec(v___y_2692_);
                        v___x_2762_ = crate::leanh::lean_box(0);
                        v_isShared_2763_ = v_isSharedCheck_2773_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2764_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                crate::leanh::lean_inc(v_activeTags_2712_);
                crate::leanh::lean_inc(v_tagStack_2759_);
                v___x_2765_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_tagStack_2759_,
                    v_tagStack_2759_,
                    v_activeTags_2712_,
                    v___x_2764_,
                );
                v___x_2766_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2759_);
                crate::leanh::lean_dec(v_tagStack_2759_);
                v_out_x27_2767_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_2758_, v___x_2765_);
                if v_isShared_2763_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2762_, 1, v___x_2766_);
                    crate::leanh::lean_ctor_set(v___x_2762_, 0, v_out_x27_2767_);
                    v___x_2769_ = v___x_2762_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2772_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_out_x27_2767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 1, v___x_2766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_column_2760_);
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
                crate::leanh::lean_inc(v_activeTags_2712_);
                crate::leanh::lean_inc(v_tagStack_2775_);
                v___x_2781_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_tagStack_2775_,
                    v_tagStack_2775_,
                    v_activeTags_2712_,
                    v___x_2780_,
                );
                v___x_2782_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2775_);
                crate::leanh::lean_dec(v_tagStack_2775_);
                v_out_x27_2783_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v_out_2774_, v___x_2781_);
                if v_isShared_2779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2778_, 1, v___x_2782_);
                    crate::leanh::lean_ctor_set(v___x_2778_, 0, v_out_x27_2783_);
                    v___x_2785_ = v___x_2778_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2788_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_out_x27_2783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_column_2776_);
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
                crate::leanh::lean_dec(v_indent_2711_);
                v___x_2797_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                crate::leanh::lean_inc(v___x_2796_);
                v___x_2798_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2796_, v___x_2797_);
                v___x_2799_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2798_, v_out_2791_);
                v___x_2800_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                crate::leanh::lean_inc(v_activeTags_2712_);
                crate::leanh::lean_inc(v_tagStack_2792_);
                v___x_2801_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_tagStack_2792_,
                    v_tagStack_2792_,
                    v_activeTags_2712_,
                    v___x_2800_,
                );
                v___x_2802_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2792_);
                crate::leanh::lean_dec(v_tagStack_2792_);
                v_out_x27_2803_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2799_, v___x_2801_);
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v___x_2796_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v___x_2802_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v_out_x27_2803_);
                    v___x_2805_ = v___x_2794_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_out_x27_2803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 1, v___x_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 2, v___x_2796_);
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
                v___x_2819_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2820_ = lean_nat_add(v_column_2813_, v___x_2819_);
                crate::leanh::lean_dec(v_column_2813_);
                v___x_2821_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                crate::leanh::lean_inc(v_activeTags_2712_);
                crate::leanh::lean_inc(v_tagStack_2812_);
                v___x_2822_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_tagStack_2812_,
                    v_tagStack_2812_,
                    v_activeTags_2712_,
                    v___x_2821_,
                );
                v___x_2823_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2812_);
                crate::leanh::lean_dec(v_tagStack_2812_);
                v_out_x27_2824_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2818_, v___x_2822_);
                if v_isShared_2816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2815_, 2, v___x_2820_);
                    crate::leanh::lean_ctor_set(v___x_2815_, 1, v___x_2823_);
                    crate::leanh::lean_ctor_set(v___x_2815_, 0, v_out_x27_2824_);
                    v___x_2826_ = v___x_2815_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2829_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_out_x27_2824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 1, v___x_2823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 2, v___x_2820_);
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
                crate::leanh::lean_inc(v___x_2831_);
                v___x_2839_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2831_, v___x_2838_);
                v___x_2840_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2839_, v_out_2833_);
                v___x_2841_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                crate::leanh::lean_inc(v_activeTags_2712_);
                crate::leanh::lean_inc(v_tagStack_2834_);
                v___x_2842_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_tagStack_2834_,
                    v_tagStack_2834_,
                    v_activeTags_2712_,
                    v___x_2841_,
                );
                v___x_2843_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2834_);
                crate::leanh::lean_dec(v_tagStack_2834_);
                v_out_x27_2844_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2840_, v___x_2842_);
                if v_isShared_2837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2836_, 2, v___x_2831_);
                    crate::leanh::lean_ctor_set(v___x_2836_, 1, v___x_2843_);
                    crate::leanh::lean_ctor_set(v___x_2836_, 0, v_out_x27_2844_);
                    v___x_2846_ = v___x_2836_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_out_x27_2844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2843_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 2, v___x_2831_);
                    v___x_2846_ = v_reuseFailAlloc_2851_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2847_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_2705_, v_tail_2706_, v_tail_2700_, v_w_2690_, v___x_2846_);
                v_fst_2848_ = crate::leanh::lean_ctor_get(v___x_2847_, 0);
                crate::leanh::lean_inc(v_fst_2848_);
                v_snd_2849_ = crate::leanh::lean_ctor_get(v___x_2847_, 1);
                crate::leanh::lean_inc(v_snd_2849_);
                crate::leanh::lean_dec_ref(v___x_2847_);
                v_x_2691_ = v_fst_2848_;
                v___y_2692_ = v_snd_2849_;
                state = 0;
                continue;
            }
            19 => {
                v___x_2868_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                crate::leanh::lean_inc(v___x_2831_);
                v___x_2869_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2831_, v___x_2868_);
                v___x_2870_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2869_, v_out_2863_);
                v___x_2871_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                crate::leanh::lean_inc(v_activeTags_2712_);
                crate::leanh::lean_inc(v_tagStack_2864_);
                v___x_2872_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_tagStack_2864_,
                    v_tagStack_2864_,
                    v_activeTags_2712_,
                    v___x_2871_,
                );
                v___x_2873_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2864_);
                crate::leanh::lean_dec(v_tagStack_2864_);
                v_out_x27_2874_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2870_, v___x_2872_);
                if v_isShared_2867_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2866_, 2, v___x_2831_);
                    crate::leanh::lean_ctor_set(v___x_2866_, 1, v___x_2873_);
                    crate::leanh::lean_ctor_set(v___x_2866_, 0, v_out_x27_2874_);
                    v___x_2876_ = v___x_2866_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2881_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_out_x27_2874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 1, v___x_2873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 2, v___x_2831_);
                    v___x_2876_ = v_reuseFailAlloc_2881_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_2877_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_2705_, v_tail_2706_, v_tail_2700_, v_w_2690_, v___x_2876_);
                v_fst_2878_ = crate::leanh::lean_ctor_get(v___x_2877_, 0);
                crate::leanh::lean_inc(v_fst_2878_);
                v_snd_2879_ = crate::leanh::lean_ctor_get(v___x_2877_, 1);
                crate::leanh::lean_inc(v_snd_2879_);
                crate::leanh::lean_dec_ref(v___x_2877_);
                v_x_2691_ = v_fst_2878_;
                v___y_2692_ = v_snd_2879_;
                state = 0;
                continue;
            }
            21 => {
                v___x_2890_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2854_, v_out_2884_);
                v___x_2891_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2892_ = lean_nat_add(v_column_2886_, v___x_2891_);
                crate::leanh::lean_dec(v_column_2886_);
                v___x_2893_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                crate::leanh::lean_inc(v_activeTags_2712_);
                crate::leanh::lean_inc(v_tagStack_2885_);
                v___x_2894_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_tagStack_2885_,
                    v_tagStack_2885_,
                    v_activeTags_2712_,
                    v___x_2893_,
                );
                v___x_2895_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2885_);
                crate::leanh::lean_dec(v_tagStack_2885_);
                v_out_x27_2896_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2890_, v___x_2894_);
                if v_isShared_2889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2888_, 2, v___x_2892_);
                    crate::leanh::lean_ctor_set(v___x_2888_, 1, v___x_2895_);
                    crate::leanh::lean_ctor_set(v___x_2888_, 0, v_out_x27_2896_);
                    v___x_2898_ = v___x_2888_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2900_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_out_x27_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 2, v___x_2892_);
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
                crate::leanh::lean_inc_ref(v_a_2907_);
                v_p_2912_ = lean_string_posof(v_a_2907_, v___x_2911_);
                v___x_2913_ = lean_string_utf8_byte_size(v_a_2907_);
                v___x_2914_ = lean_nat_dec_eq(v_p_2912_, v___x_2913_);
                if v___x_2914_ == 0 {
                    v_out_2915_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_2916_ = crate::leanh::lean_ctor_get(v___y_2692_, 1);
                    v_isSharedCheck_2949_ = (!crate::leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_2949_ == 0 {
                        v_unused_2950_ = crate::leanh::lean_ctor_get(v___y_2692_, 2);
                        crate::leanh::lean_dec(v_unused_2950_);
                        v___x_2918_ = v___y_2692_;
                        v_isShared_2919_ = v_isSharedCheck_2949_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tagStack_2916_);
                        crate::leanh::lean_inc(v_out_2915_);
                        crate::leanh::lean_dec(v___y_2692_);
                        v___x_2918_ = crate::leanh::lean_box(0);
                        v_isShared_2919_ = v_isSharedCheck_2949_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_p_2912_);
                    crate::leanh::lean_del_object(v___x_2909_);
                    crate::leanh::lean_del_object(v___x_2714_);
                    crate::leanh::lean_dec(v_indent_2711_);
                    crate::leanh::lean_del_object(v___x_2708_);
                    v_out_2951_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
                    v_tagStack_2952_ = crate::leanh::lean_ctor_get(v___y_2692_, 1);
                    v_column_2953_ = crate::leanh::lean_ctor_get(v___y_2692_, 2);
                    v_isSharedCheck_2969_ = (!crate::leanh::lean_is_exclusive(v___y_2692_)) as u8;
                    if v_isSharedCheck_2969_ == 0 {
                        v___x_2955_ = v___y_2692_;
                        v_isShared_2956_ = v_isSharedCheck_2969_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_column_2953_);
                        crate::leanh::lean_inc(v_tagStack_2952_);
                        crate::leanh::lean_inc(v_out_2951_);
                        crate::leanh::lean_dec(v___y_2692_);
                        v___x_2955_ = crate::leanh::lean_box(0);
                        v_isShared_2956_ = v_isSharedCheck_2969_;
                        state = 29;
                        continue;
                    }
                }
            }
            24 => {
                v___x_2920_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2921_ = lean_string_utf8_extract(v_a_2907_, v___x_2920_, v_p_2912_);
                v___x_2922_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2921_, v_out_2915_);
                v___x_2923_ = l_Int_toNat(v_indent_2711_);
                v___x_2924_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__0;
                crate::leanh::lean_inc(v___x_2923_);
                v___x_2925_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__2(v___x_2923_, v___x_2924_);
                v___x_2926_ =
                    l_Lean_Widget_TaggedText_appendText___redArg(v___x_2925_, v___x_2922_);
                if v_isShared_2919_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2918_, 2, v___x_2923_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 0, v___x_2926_);
                    v___x_2928_ = v___x_2918_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2948_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_tagStack_2916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 2, v___x_2923_);
                    v___x_2928_ = v_reuseFailAlloc_2948_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_2929_ = lean_string_utf8_next(v_a_2907_, v_p_2912_);
                crate::leanh::lean_dec(v_p_2912_);
                v___x_2930_ = lean_string_utf8_extract(v_a_2907_, v___x_2929_, v___x_2913_);
                crate::leanh::lean_dec(v___x_2929_);
                crate::leanh::lean_dec_ref(v_a_2907_);
                if v_isShared_2910_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2909_, 0, v___x_2930_);
                    v___x_2932_ = v___x_2909_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2930_);
                    v___x_2932_ = v_reuseFailAlloc_2947_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_2715_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2714_, 0, v___x_2932_);
                    v___x_2934_ = v___x_2714_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2946_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_indent_2711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_activeTags_2712_);
                    v___x_2934_ = v_reuseFailAlloc_2946_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_2934_);
                    v_is_2936_ = v___x_2708_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2945_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_tail_2706_);
                    v_is_2936_ = v_reuseFailAlloc_2945_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_2937_ = crate::leanh::lean_box(1);
                v___x_2938_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_2704_, v___x_2937_);
                if v___x_2938_ == 0 {
                    crate::leanh::lean_dec(v_fla_2704_);
                    v___x_2939_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_flb_2705_, v_is_2936_, v_tail_2700_, v_w_2690_, v___x_2928_);
                    v_fst_2940_ = crate::leanh::lean_ctor_get(v___x_2939_, 0);
                    crate::leanh::lean_inc(v_fst_2940_);
                    v_snd_2941_ = crate::leanh::lean_ctor_get(v___x_2939_, 1);
                    crate::leanh::lean_inc(v_snd_2941_);
                    crate::leanh::lean_dec_ref(v___x_2939_);
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
                crate::leanh::lean_inc_ref(v_a_2907_);
                v___x_2957_ = l_Lean_Widget_TaggedText_appendText___redArg(v_a_2907_, v_out_2951_);
                v___x_2958_ = lean_string_length(v_a_2907_);
                crate::leanh::lean_dec_ref(v_a_2907_);
                v___x_2959_ = lean_nat_add(v_column_2953_, v___x_2958_);
                crate::leanh::lean_dec(v_column_2953_);
                v___x_2960_ = l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__6___closed__0;
                crate::leanh::lean_inc(v_activeTags_2712_);
                crate::leanh::lean_inc(v_tagStack_2952_);
                v___x_2961_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    crate::leanh::lean_box(0),
                    v_tagStack_2952_,
                    v_tagStack_2952_,
                    v_activeTags_2712_,
                    v___x_2960_,
                );
                v___x_2962_ = l_List_drop___redArg(v_activeTags_2712_, v_tagStack_2952_);
                crate::leanh::lean_dec(v_tagStack_2952_);
                v_out_x27_2963_ = l_List_foldl___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__3(v___x_2957_, v___x_2961_);
                if v_isShared_2956_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2955_, 2, v___x_2959_);
                    crate::leanh::lean_ctor_set(v___x_2955_, 1, v___x_2962_);
                    crate::leanh::lean_ctor_set(v___x_2955_, 0, v_out_x27_2963_);
                    v___x_2965_ = v___x_2955_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2968_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_out_x27_2963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2968_, 2, v___x_2959_);
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
                    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_2975_);
                    v___x_2977_ = v___x_2708_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2980_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_tail_2706_);
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
                v___x_2987_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2987_, 0, v_a_2983_);
                crate::leanh::lean_ctor_set(v___x_2987_, 1, v_indent_2711_);
                crate::leanh::lean_ctor_set(v___x_2987_, 2, v_activeTags_2712_);
                if v_isShared_2709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_2987_);
                    v___x_2989_ = v___x_2708_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2995_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_tail_2706_);
                    v___x_2989_ = v_reuseFailAlloc_2995_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_2703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2702_, 1, v___x_2989_);
                    crate::leanh::lean_ctor_set(v___x_2702_, 0, v___x_2986_);
                    v___x_2991_ = v___x_2702_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2994_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___x_2989_);
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
                v___x_3002_ = crate::leanh::lean_box(0);
                if v_isShared_2709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2708_, 1, v___x_3002_);
                    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_3001_);
                    v___x_3004_ = v___x_2708_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3010_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___x_3002_);
                    v___x_3004_ = v_reuseFailAlloc_3010_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_3005_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1___lam__0(v_fla_2704_, v_flb_2705_, v_tail_2700_, v_tail_2706_);
                v___x_3006_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1_spec__4(v_behavior_2998_, v___x_3004_, v___x_3005_, v_w_2690_, v___y_2692_);
                v_fst_3007_ = crate::leanh::lean_ctor_get(v___x_3006_, 0);
                crate::leanh::lean_inc(v_fst_3007_);
                v_snd_3008_ = crate::leanh::lean_ctor_get(v___x_3006_, 1);
                crate::leanh::lean_inc(v_snd_3008_);
                crate::leanh::lean_dec_ref(v___x_3006_);
                v_x_2691_ = v_fst_3007_;
                v___y_2692_ = v_snd_3008_;
                state = 0;
                continue;
            }
            38 => {
                if v_isShared_2709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_3013_);
                    v___x_3015_ = v___x_2708_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_tail_2706_);
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
                crate::leanh::lean_inc(v_column_3024_);
                v___x_3029_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3029_, 0, v_column_3024_);
                crate::leanh::lean_ctor_set(v___x_3029_, 1, v_out_3022_);
                v___x_3030_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3030_, 0, v_a_3020_);
                crate::leanh::lean_ctor_set(v___x_3030_, 1, v___x_3029_);
                if v_isShared_2709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2708_, 1, v_tagStack_3023_);
                    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_3030_);
                    v___x_3032_ = v___x_2708_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_tagStack_3023_);
                    v___x_3032_ = v_reuseFailAlloc_3046_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_3027_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3026_, 1, v___x_3032_);
                    crate::leanh::lean_ctor_set(v___x_3026_, 0, v___x_3028_);
                    v___x_3034_ = v___x_3026_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3045_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 2, v_column_3024_);
                    v___x_3034_ = v_reuseFailAlloc_3045_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v___x_3035_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3036_ = lean_nat_add(v_activeTags_2712_, v___x_3035_);
                crate::leanh::lean_dec(v_activeTags_2712_);
                if v_isShared_2715_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2714_, 2, v___x_3036_);
                    crate::leanh::lean_ctor_set(v___x_2714_, 0, v_a_3021_);
                    v___x_3038_ = v___x_2714_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3044_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_indent_2711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 2, v___x_3036_);
                    v___x_3038_ = v_reuseFailAlloc_3044_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_2703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2702_, 1, v_tail_2706_);
                    crate::leanh::lean_ctor_set(v___x_2702_, 0, v___x_3038_);
                    v___x_3040_ = v___x_2702_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3043_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_tail_2706_);
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
    mut v_w_3053_: *mut crate::leanh::LeanObject,
    mut v_x_3054_: *mut crate::leanh::LeanObject,
    mut v___y_3055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_3053_, v_x_3054_, v___y_3055_);
    crate::leanh::lean_dec(v_w_3053_);
    return v_res_3056_;
}
pub unsafe fn l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(
    mut v_f_3057_: *mut crate::leanh::LeanObject,
    mut v_w_3058_: *mut crate::leanh::LeanObject,
    mut v_indent_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: u8 = 0;
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3061_ = crate::leanh::lean_box(1);
    v___x_3062_ = 0;
    v___x_3063_ = lean_nat_to_int(v_indent_3059_);
    v___x_3064_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3065_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3065_, 0, v_f_3057_);
    crate::leanh::lean_ctor_set(v___x_3065_, 1, v___x_3063_);
    crate::leanh::lean_ctor_set(v___x_3065_, 2, v___x_3064_);
    v___x_3066_ = crate::leanh::lean_box(0);
    v___x_3067_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3067_, 0, v___x_3065_);
    crate::leanh::lean_ctor_set(v___x_3067_, 1, v___x_3066_);
    v___x_3068_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3068_, 0, v___x_3061_);
    crate::leanh::lean_ctor_set(v___x_3068_, 1, v___x_3067_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3068_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_3062_,
    );
    v___x_3069_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3068_);
    crate::leanh::lean_ctor_set(v___x_3069_, 1, v___x_3066_);
    v___x_3070_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__1(v_w_3058_, v___x_3069_, v___y_3060_);
    return v___x_3070_;
}
pub unsafe fn l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0___boxed(
    mut v_f_3071_: *mut crate::leanh::LeanObject,
    mut v_w_3072_: *mut crate::leanh::LeanObject,
    mut v_indent_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(
        v_f_3071_,
        v_w_3072_,
        v_indent_3073_,
        v___y_3074_,
    );
    crate::leanh::lean_dec(v_w_3072_);
    return v_res_3075_;
}
pub unsafe fn l_Lean_Widget_TaggedText_prettyTagged(
    mut v_f_3076_: *mut crate::leanh::LeanObject,
    mut v_indent_3077_: *mut crate::leanh::LeanObject,
    mut v_w_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3079_ = l_Lean_Widget_TaggedText_instInhabitedTaggedState_default___closed__1;
    v___x_3080_ = l_Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0(
        v_f_3076_,
        v_w_3078_,
        v_indent_3077_,
        v___x_3079_,
    );
    v_snd_3081_ = crate::leanh::lean_ctor_get(v___x_3080_, 1);
    crate::leanh::lean_inc(v_snd_3081_);
    crate::leanh::lean_dec_ref(v___x_3080_);
    v_out_3082_ = crate::leanh::lean_ctor_get(v_snd_3081_, 0);
    crate::leanh::lean_inc_ref(v_out_3082_);
    crate::leanh::lean_dec(v_snd_3081_);
    return v_out_3082_;
}
pub unsafe fn l_Lean_Widget_TaggedText_prettyTagged___boxed(
    mut v_f_3083_: *mut crate::leanh::LeanObject,
    mut v_indent_3084_: *mut crate::leanh::LeanObject,
    mut v_w_3085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3086_ = l_Lean_Widget_TaggedText_prettyTagged(v_f_3083_, v_indent_3084_, v_w_3085_);
    crate::leanh::lean_dec(v_w_3085_);
    return v_res_3086_;
}
pub unsafe fn l_Nat_cast___at___00Std_Format_prettyM___at___00Lean_Widget_TaggedText_prettyTagged_spec__0_spec__0(
    mut v_a_3087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3088_ = lean_nat_to_int(v_a_3087_);
    return v___x_3088_;
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(
    mut v_acc_3089_: *mut crate::leanh::LeanObject,
    mut v_a_3090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3091_ = lean_array_get_size(v_a_3090_);
                v___x_3092_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3093_ = lean_nat_dec_eq(v___x_3091_, v___x_3092_);
                if v___x_3093_ == 0 {
                    v___x_3094_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Widget_instInhabitedTaggedText___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_instInhabitedTaggedText___closed__0_once
                        ),
                        _init_l_Lean_Widget_instInhabitedTaggedText___closed__0,
                    );
                    v___x_3095_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3096_ = lean_nat_sub(v___x_3091_, v___x_3095_);
                    v___x_3097_ = lean_array_get_borrowed(v___x_3094_, v_a_3090_, v___x_3096_);
                    match crate::leanh::lean_obj_tag(v___x_3097_) {
                        0 => {
                            crate::leanh::lean_dec(v___x_3096_);
                            v_a_3098_ = crate::leanh::lean_ctor_get(v___x_3097_, 0);
                            v___x_3099_ = lean_string_append(v_acc_3089_, v_a_3098_);
                            v___x_3100_ = lean_array_pop(v_a_3090_);
                            v_acc_3089_ = v___x_3099_;
                            v_a_3090_ = v___x_3100_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v___x_3096_);
                            v_a_3102_ = crate::leanh::lean_ctor_get(v___x_3097_, 0);
                            crate::leanh::lean_inc_ref(v_a_3102_);
                            v___x_3103_ = lean_array_pop(v_a_3090_);
                            v___x_3104_ = l_Array_reverse___redArg(v_a_3102_);
                            v___x_3105_ = l_Array_append___redArg(v___x_3103_, v___x_3104_);
                            crate::leanh::lean_dec_ref(v___x_3104_);
                            v_a_3090_ = v___x_3105_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v_a_3107_ = crate::leanh::lean_ctor_get(v___x_3097_, 1);
                            crate::leanh::lean_inc_ref(v_a_3107_);
                            v___x_3108_ = lean_array_set(v_a_3090_, v___x_3096_, v_a_3107_);
                            crate::leanh::lean_dec(v___x_3096_);
                            v_a_3090_ = v___x_3108_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_3090_);
                    return v_acc_3089_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go(
    mut v_00_u03b1_3110_: *mut crate::leanh::LeanObject,
    mut v_acc_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3113_ =
        l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_stripTags_go___redArg(
            v_acc_3111_,
            v_a_3112_,
        );
    return v___x_3113_;
}
pub unsafe fn l_Lean_Widget_TaggedText_stripTags___redArg(
    mut v_tt_3114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3115_ = l_Lean_Widget_instInhabitedTaggedText_default___closed__0;
    v___x_3116_ = crate::leanh::lean_unsigned_to_nat(1);
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
    mut v_00_u03b1_3120_: *mut crate::leanh::LeanObject,
    mut v_tt_3121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3122_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_3121_);
    return v___x_3122_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_TaggedText(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Rpc_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_GetLit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1 = _init_l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1();
    crate::leanh::lean_mark_persistent(l___private_Lean_Widget_TaggedText_0__Lean_Widget_TaggedText_instMonadPrettyFormatStateMTaggedState___lam__2___closed__1___boxed__const__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_TaggedText(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_TaggedText(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Rpc_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_GetLit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_TaggedText(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_TaggedText(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Widget_TaggedText(builtin);
}
