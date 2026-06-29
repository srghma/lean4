// Lean compiler output
// Module: Lean.Data.FuzzyMatching
// Imports: Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Nat Init.Data.OfScientific Init.Data.Option.Coe Init.Data.Range Lean.Server.Completion.CompletionUtils
use crate::ffi::{
    lean_array_get, lean_array_push, lean_array_set, lean_float_decLe, lean_float_decLt,
    lean_float_div, lean_int_mul, lean_int16_add, lean_int16_dec_eq, lean_int16_dec_le,
    lean_int16_neg, lean_int16_of_nat, lean_int16_sub, lean_int16_to_int, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_shiftr, lean_nat_sub, lean_nat_to_int,
    lean_panic_fn_borrowed, lean_string_length, lean_string_utf8_at_end,
    lean_string_utf8_byte_size, lean_string_utf8_get, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_uint32_add, lean_uint32_dec_eq, lean_uint32_dec_le,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::OfScientific::{
    initialize_Init_Data_OfScientific, l_Float_ofInt, lean_float_of_nat,
    runtime_initialize_Init_Data_OfScientific,
};
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Data::Range::Basic::l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Nat::{
    initialize_Init_Data_Range_Polymorphic_Nat, runtime_initialize_Init_Data_Range_Polymorphic_Nat,
};
use crate::r#gen::Init::Data::Range::{
    initialize_Init_Data_Range, runtime_initialize_Init_Data_Range,
};
use crate::r#gen::Init::Data::SInt::Basic::l_instInhabitedInt16;
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Server::Completion::CompletionUtils::{
    initialize_Lean_Server_Completion_CompletionUtils, l_String_charactersIn,
    runtime_initialize_Lean_Server_Completion_CompletionUtils,
};
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_FuzzyMatching_instInhabitedCharRole_default: u8 = 0;
pub static mut l_Lean_FuzzyMatching_instInhabitedCharRole: u8 = 0;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0: u16 = 0;
pub static mut l_Lean_FuzzyMatching_instInhabitedScore_default: u16 = 0;
pub static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore: u16 =
    0;
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0: u16 =
    0;
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1: u16 =
    0;
pub static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful: u16 = 0;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 70, 117, 122, 122, 121, 77, 97, 116, 99, 104, 105, 110, 103, 0]};
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1_value: crate::leanh::LeanStringObject<69> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 70, 117, 122, 122, 121, 77, 97, 116, 99, 104, 105, 110, 103, 46, 48, 46, 76, 101, 97, 110, 46, 70, 117, 122, 122, 121, 77, 97, 116, 99, 104, 105, 110, 103, 46, 83, 99, 111, 114, 101, 46, 111, 102, 73, 110, 116, 49, 54, 33, 0]};
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 120, 32, 33, 61, 32, 97, 119, 102, 117, 108, 46, 105, 110, 110, 101, 114, 10, 32, 32, 0]};
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0: u16 = 0;
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1: u16 = 0;
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0: u16 = 0;
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1: u16 = 0;
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0: f64 = 0.0;
static mut l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1: f64 = 0.0;
static mut l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0(
    mut v___x_1441_: *mut crate::leanh::LeanObject,
    mut v_string_1442_: *mut crate::leanh::LeanObject,
    mut v___x_1443_: *mut crate::leanh::LeanObject,
    mut v_f_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
    mut v_x_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u32 = 0;
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: u32 = 0;
    let mut v___x_1454_: u32 = 0;
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = lean_nat_sub(v_a_1445_, v___x_1441_);
    v___x_1449_ = lean_string_utf8_get(v_string_1442_, v___x_1448_);
    crate::leanh::lean_dec(v___x_1448_);
    v___x_1450_ = crate::leanh::lean_box_uint32(v___x_1449_);
    v___x_1451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1451_, 0, v___x_1450_);
    v___x_1452_ = lean_nat_sub(v_a_1445_, v___x_1443_);
    v___x_1453_ = lean_string_utf8_get(v_string_1442_, v___x_1452_);
    crate::leanh::lean_dec(v___x_1452_);
    v___x_1454_ = lean_string_utf8_get(v_string_1442_, v_a_1445_);
    v___x_1455_ = crate::leanh::lean_box_uint32(v___x_1454_);
    v___x_1456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1456_, 0, v___x_1455_);
    v___x_1457_ = crate::leanh::lean_box_uint32(v___x_1453_);
    v___x_1458_ = crate::leanh::lean_apply_3(v_f_1444_, v___x_1451_, v___x_1457_, v___x_1456_);
    v___x_1459_ = lean_array_push(v___y_1447_, v___x_1458_);
    v___x_1460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0___boxed(
    mut v___x_1461_: *mut crate::leanh::LeanObject,
    mut v_string_1462_: *mut crate::leanh::LeanObject,
    mut v___x_1463_: *mut crate::leanh::LeanObject,
    mut v_f_1464_: *mut crate::leanh::LeanObject,
    mut v_a_1465_: *mut crate::leanh::LeanObject,
    mut v_x_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1468_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0(v___x_1461_, v_string_1462_, v___x_1463_, v_f_1464_, v_a_1465_, v_x_1466_, v___y_1467_);
    crate::leanh::lean_dec(v_a_1465_);
    crate::leanh::lean_dec(v___x_1463_);
    crate::leanh::lean_dec_ref(v_string_1462_);
    crate::leanh::lean_dec(v___x_1461_);
    return v_res_1468_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg(
    mut v_f_1490_: *mut crate::leanh::LeanObject,
    mut v_string_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    v___x_1492_ = lean_string_utf8_byte_size(v_string_1491_);
    v___x_1493_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1494_ = lean_nat_dec_eq(v___x_1492_, v___x_1493_);
    if v___x_1494_ == 0 {
        let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: u8 = 0;
        v___x_1495_ = lean_string_length(v_string_1491_);
        v___x_1496_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1497_ = lean_nat_dec_eq(v___x_1495_, v___x_1496_);
        if v___x_1497_ == 0 {
            let mut v_result_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1500_: u32 = 0;
            let mut v___x_1501_: u32 = 0;
            let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_result_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1513_: u32 = 0;
            let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1517_: u32 = 0;
            let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_result_1498_ = lean_mk_empty_array_with_capacity(v___x_1495_);
            v___x_1499_ = crate::leanh::lean_box(0);
            v___x_1500_ = lean_string_utf8_get(v_string_1491_, v___x_1493_);
            v___x_1501_ = lean_string_utf8_get(v_string_1491_, v___x_1496_);
            v___x_1502_ = crate::leanh::lean_box_uint32(v___x_1501_);
            v___x_1503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1503_, 0, v___x_1502_);
            v___x_1504_ = crate::leanh::lean_box_uint32(v___x_1500_);
            crate::leanh::lean_inc_n(v_f_1490_, 2);
            v___x_1505_ =
                crate::leanh::lean_apply_3(v_f_1490_, v___x_1499_, v___x_1504_, v___x_1503_);
            v_result_1506_ = lean_array_push(v_result_1498_, v___x_1505_);
            v___x_1507_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__9;
            v___x_1508_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc_ref(v_string_1491_);
            v___f_1509_ = crate::leanh::lean_alloc_closure(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 4);
            crate::leanh::lean_closure_set(v___f_1509_, 0, v___x_1508_);
            crate::leanh::lean_closure_set(v___f_1509_, 1, v_string_1491_);
            crate::leanh::lean_closure_set(v___f_1509_, 2, v___x_1496_);
            crate::leanh::lean_closure_set(v___f_1509_, 3, v_f_1490_);
            v___x_1510_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1508_);
            crate::leanh::lean_ctor_set(v___x_1510_, 1, v___x_1495_);
            crate::leanh::lean_ctor_set(v___x_1510_, 2, v___x_1496_);
            v___x_1511_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1507_,
                v___x_1510_,
                v___f_1509_,
                v_result_1506_,
                v___x_1508_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            v___x_1512_ = lean_nat_sub(v___x_1495_, v___x_1508_);
            v___x_1513_ = lean_string_utf8_get(v_string_1491_, v___x_1512_);
            crate::leanh::lean_dec(v___x_1512_);
            v___x_1514_ = crate::leanh::lean_box_uint32(v___x_1513_);
            v___x_1515_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1515_, 0, v___x_1514_);
            v___x_1516_ = lean_nat_sub(v___x_1495_, v___x_1496_);
            v___x_1517_ = lean_string_utf8_get(v_string_1491_, v___x_1516_);
            crate::leanh::lean_dec(v___x_1516_);
            crate::leanh::lean_dec_ref(v_string_1491_);
            v___x_1518_ = crate::leanh::lean_box_uint32(v___x_1517_);
            v___x_1519_ =
                crate::leanh::lean_apply_3(v_f_1490_, v___x_1515_, v___x_1518_, v___x_1499_);
            v___x_1520_ = lean_array_push(v___x_1511_, v___x_1519_);
            return v___x_1520_;
        } else {
            let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1522_: u32 = 0;
            let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1521_ = crate::leanh::lean_box(0);
            v___x_1522_ = lean_string_utf8_get(v_string_1491_, v___x_1493_);
            crate::leanh::lean_dec_ref(v_string_1491_);
            v___x_1523_ = crate::leanh::lean_box_uint32(v___x_1522_);
            v___x_1524_ =
                crate::leanh::lean_apply_3(v_f_1490_, v___x_1521_, v___x_1523_, v___x_1521_);
            v___x_1525_ = lean_mk_empty_array_with_capacity(v___x_1496_);
            v___x_1526_ = lean_array_push(v___x_1525_, v___x_1524_);
            return v___x_1526_;
        }
    } else {
        let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_string_1491_);
        crate::leanh::lean_dec(v_f_1490_);
        v___x_1527_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg___closed__10;
        return v___x_1527_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround(
    mut v_00_u03b1_1528_: *mut crate::leanh::LeanObject,
    mut v_f_1529_: *mut crate::leanh::LeanObject,
    mut v_string_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___redArg(
            v_f_1529_,
            v_string_1530_,
        );
    return v___x_1531_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_b_1533_: *mut crate::leanh::LeanObject,
    mut v_aPos_1534_: *mut crate::leanh::LeanObject,
    mut v_bPos_1535_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: u8 = 0;
    let mut v_ac_1538_: u32 = 0;
    let mut v_bc_1539_: u32 = 0;
    let mut v_bPos_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1542_: u32 = 0;
    let mut v___y_1543_: u32 = 0;
    let mut v___x_1544_: u8 = 0;
    let mut v_aPos_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1549_: u32 = 0;
    let mut v___x_1550_: u32 = 0;
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1552_: u32 = 0;
    let mut v___x_1553_: u8 = 0;
    let mut v___x_1554_: u32 = 0;
    let mut v___x_1555_: u32 = 0;
    let mut v___x_1556_: u32 = 0;
    let mut v___x_1557_: u8 = 0;
    let mut v___x_1558_: u32 = 0;
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1560_: u32 = 0;
    let mut v___x_1561_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1536_ = lean_string_utf8_at_end(v_a_1532_, v_aPos_1534_);
                if v___x_1536_ == 0 {
                    v___x_1537_ = lean_string_utf8_at_end(v_b_1533_, v_bPos_1535_);
                    if v___x_1537_ == 0 {
                        v_ac_1538_ = lean_string_utf8_get_fast(v_a_1532_, v_aPos_1534_);
                        v_bc_1539_ = lean_string_utf8_get_fast(v_b_1533_, v_bPos_1535_);
                        v_bPos_1540_ = lean_string_utf8_next_fast(v_b_1533_, v_bPos_1535_);
                        crate::leanh::lean_dec(v_bPos_1535_);
                        v___x_1556_ = 65;
                        v___x_1557_ = lean_uint32_dec_le(v___x_1556_, v_ac_1538_);
                        if v___x_1557_ == 0 {
                            v___y_1549_ = v_ac_1538_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1558_ = 90;
                            v___x_1559_ = lean_uint32_dec_le(v_ac_1538_, v___x_1558_);
                            if v___x_1559_ == 0 {
                                v___y_1549_ = v_ac_1538_;
                                state = 2;
                                continue;
                            } else {
                                v___x_1560_ = 32;
                                v___x_1561_ = lean_uint32_add(v_ac_1538_, v___x_1560_);
                                v___y_1549_ = v___x_1561_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_bPos_1535_);
                        crate::leanh::lean_dec(v_aPos_1534_);
                        return v___x_1536_;
                    }
                } else {
                    crate::leanh::lean_dec(v_bPos_1535_);
                    crate::leanh::lean_dec(v_aPos_1534_);
                    return v___x_1536_;
                }
            }
            1 => {
                v___x_1544_ = lean_uint32_dec_eq(v___y_1542_, v___y_1543_);
                if v___x_1544_ == 0 {
                    v_bPos_1535_ = v_bPos_1540_;
                    state = 0;
                    continue;
                } else {
                    v_aPos_1546_ = lean_string_utf8_next_fast(v_a_1532_, v_aPos_1534_);
                    crate::leanh::lean_dec(v_aPos_1534_);
                    v_aPos_1534_ = v_aPos_1546_;
                    v_bPos_1535_ = v_bPos_1540_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_1550_ = 65;
                v___x_1551_ = lean_uint32_dec_le(v___x_1550_, v_bc_1539_);
                if v___x_1551_ == 0 {
                    v___y_1542_ = v___y_1549_;
                    v___y_1543_ = v_bc_1539_;
                    state = 1;
                    continue;
                } else {
                    v___x_1552_ = 90;
                    v___x_1553_ = lean_uint32_dec_le(v_bc_1539_, v___x_1552_);
                    if v___x_1553_ == 0 {
                        v___y_1542_ = v___y_1549_;
                        v___y_1543_ = v_bc_1539_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1554_ = 32;
                        v___x_1555_ = lean_uint32_add(v_bc_1539_, v___x_1554_);
                        v___y_1542_ = v___y_1549_;
                        v___y_1543_ = v___x_1555_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go___boxed(
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_b_1563_: *mut crate::leanh::LeanObject,
    mut v_aPos_1564_: *mut crate::leanh::LeanObject,
    mut v_bPos_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1566_: u8 = 0;
    let mut v_r_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(
        v_a_1562_,
        v_b_1563_,
        v_aPos_1564_,
        v_bPos_1565_,
    );
    crate::leanh::lean_dec_ref(v_b_1563_);
    crate::leanh::lean_dec_ref(v_a_1562_);
    v_r_1567_ = crate::leanh::lean_box((v_res_1566_) as usize);
    return v_r_1567_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(
    mut v_a_1568_: *mut crate::leanh::LeanObject,
    mut v_b_1569_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    v___x_1570_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1571_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower_go(
        v_a_1568_,
        v_b_1569_,
        v___x_1570_,
        v___x_1570_,
    );
    return v___x_1571_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower___boxed(
    mut v_a_1572_: *mut crate::leanh::LeanObject,
    mut v_b_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1574_: u8 = 0;
    let mut v_r_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_containsInOrderLower(
        v_a_1572_, v_b_1573_,
    );
    crate::leanh::lean_dec_ref(v_b_1573_);
    crate::leanh::lean_dec_ref(v_a_1572_);
    v_r_1575_ = crate::leanh::lean_box((v_res_1574_) as usize);
    return v_r_1575_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_ctorIdx(
    mut v_x_1576_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1576_ {
        0 => {
            let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1577_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1577_;
        }
        1 => {
            let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1578_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1578_;
        }
        _ => {
            let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1579_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1579_;
        }
    }
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_ctorIdx___boxed(
    mut v_x_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1581_: u8 = 0;
    let mut v_res_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1581_ = (crate::leanh::lean_unbox(v_x_1580_) as u8);
    v_res_1582_ = l_Lean_FuzzyMatching_CharType_ctorIdx(v_x_boxed_1581_);
    return v_res_1582_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_toCtorIdx(
    mut v_x_1583_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lean_FuzzyMatching_CharType_ctorIdx(v_x_1583_);
    return v___x_1584_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_toCtorIdx___boxed(
    mut v_x_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1586_: u8 = 0;
    let mut v_res_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1586_ = (crate::leanh::lean_unbox(v_x_1585_) as u8);
    v_res_1587_ = l_Lean_FuzzyMatching_CharType_toCtorIdx(v_x_4__boxed_1586_);
    return v_res_1587_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_ctorElim___redArg(
    mut v_k_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1588_);
    return v_k_1588_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_ctorElim___redArg___boxed(
    mut v_k_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Lean_FuzzyMatching_CharType_ctorElim___redArg(v_k_1589_);
    crate::leanh::lean_dec(v_k_1589_);
    return v_res_1590_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_ctorElim(
    mut v_motive_1591_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1592_: *mut crate::leanh::LeanObject,
    mut v_t_1593_: u8,
    mut v_h_1594_: *mut crate::leanh::LeanObject,
    mut v_k_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1595_);
    return v_k_1595_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_ctorElim___boxed(
    mut v_motive_1596_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1597_: *mut crate::leanh::LeanObject,
    mut v_t_1598_: *mut crate::leanh::LeanObject,
    mut v_h_1599_: *mut crate::leanh::LeanObject,
    mut v_k_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1601_: u8 = 0;
    let mut v_res_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1601_ = (crate::leanh::lean_unbox(v_t_1598_) as u8);
    v_res_1602_ = l_Lean_FuzzyMatching_CharType_ctorElim(
        v_motive_1596_,
        v_ctorIdx_1597_,
        v_t_boxed_1601_,
        v_h_1599_,
        v_k_1600_,
    );
    crate::leanh::lean_dec(v_k_1600_);
    crate::leanh::lean_dec(v_ctorIdx_1597_);
    return v_res_1602_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_lower_elim___redArg(
    mut v_lower_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lower_1603_);
    return v_lower_1603_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_lower_elim___redArg___boxed(
    mut v_lower_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1605_ = l_Lean_FuzzyMatching_CharType_lower_elim___redArg(v_lower_1604_);
    crate::leanh::lean_dec(v_lower_1604_);
    return v_res_1605_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_lower_elim(
    mut v_motive_1606_: *mut crate::leanh::LeanObject,
    mut v_t_1607_: u8,
    mut v_h_1608_: *mut crate::leanh::LeanObject,
    mut v_lower_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lower_1609_);
    return v_lower_1609_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_lower_elim___boxed(
    mut v_motive_1610_: *mut crate::leanh::LeanObject,
    mut v_t_1611_: *mut crate::leanh::LeanObject,
    mut v_h_1612_: *mut crate::leanh::LeanObject,
    mut v_lower_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1614_: u8 = 0;
    let mut v_res_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1614_ = (crate::leanh::lean_unbox(v_t_1611_) as u8);
    v_res_1615_ = l_Lean_FuzzyMatching_CharType_lower_elim(
        v_motive_1610_,
        v_t_boxed_1614_,
        v_h_1612_,
        v_lower_1613_,
    );
    crate::leanh::lean_dec(v_lower_1613_);
    return v_res_1615_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_upper_elim___redArg(
    mut v_upper_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_upper_1616_);
    return v_upper_1616_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_upper_elim___redArg___boxed(
    mut v_upper_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1618_ = l_Lean_FuzzyMatching_CharType_upper_elim___redArg(v_upper_1617_);
    crate::leanh::lean_dec(v_upper_1617_);
    return v_res_1618_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_upper_elim(
    mut v_motive_1619_: *mut crate::leanh::LeanObject,
    mut v_t_1620_: u8,
    mut v_h_1621_: *mut crate::leanh::LeanObject,
    mut v_upper_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_upper_1622_);
    return v_upper_1622_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_upper_elim___boxed(
    mut v_motive_1623_: *mut crate::leanh::LeanObject,
    mut v_t_1624_: *mut crate::leanh::LeanObject,
    mut v_h_1625_: *mut crate::leanh::LeanObject,
    mut v_upper_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1627_: u8 = 0;
    let mut v_res_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1627_ = (crate::leanh::lean_unbox(v_t_1624_) as u8);
    v_res_1628_ = l_Lean_FuzzyMatching_CharType_upper_elim(
        v_motive_1623_,
        v_t_boxed_1627_,
        v_h_1625_,
        v_upper_1626_,
    );
    crate::leanh::lean_dec(v_upper_1626_);
    return v_res_1628_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_separator_elim___redArg(
    mut v_separator_1629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_separator_1629_);
    return v_separator_1629_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_separator_elim___redArg___boxed(
    mut v_separator_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Lean_FuzzyMatching_CharType_separator_elim___redArg(v_separator_1630_);
    crate::leanh::lean_dec(v_separator_1630_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_separator_elim(
    mut v_motive_1632_: *mut crate::leanh::LeanObject,
    mut v_t_1633_: u8,
    mut v_h_1634_: *mut crate::leanh::LeanObject,
    mut v_separator_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_separator_1635_);
    return v_separator_1635_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharType_separator_elim___boxed(
    mut v_motive_1636_: *mut crate::leanh::LeanObject,
    mut v_t_1637_: *mut crate::leanh::LeanObject,
    mut v_h_1638_: *mut crate::leanh::LeanObject,
    mut v_separator_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1640_: u8 = 0;
    let mut v_res_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1640_ = (crate::leanh::lean_unbox(v_t_1637_) as u8);
    v_res_1641_ = l_Lean_FuzzyMatching_CharType_separator_elim(
        v_motive_1636_,
        v_t_boxed_1640_,
        v_h_1638_,
        v_separator_1639_,
    );
    crate::leanh::lean_dec(v_separator_1639_);
    return v_res_1641_;
}
pub unsafe fn l_Lean_FuzzyMatching_charType(mut v_c_1642_: u32) -> u8 {
    let mut v___x_1644_: u32 = 0;
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: u32 = 0;
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: u8 = 0;
    let mut v___x_1650_: u8 = 0;
    let mut v___y_1652_: u8 = 0;
    let mut v___x_1653_: u8 = 0;
    let mut v___y_1655_: u8 = 0;
    let mut v___x_1656_: u32 = 0;
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: u32 = 0;
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1661_: u32 = 0;
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1663_: u32 = 0;
    let mut v___x_1664_: u8 = 0;
    let mut v___x_1665_: u32 = 0;
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: u32 = 0;
    let mut v___x_1668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1665_ = 65;
                v___x_1666_ = lean_uint32_dec_le(v___x_1665_, v_c_1642_);
                if v___x_1666_ == 0 {
                    state = 4;
                    continue;
                } else {
                    v___x_1667_ = 90;
                    v___x_1668_ = lean_uint32_dec_le(v_c_1642_, v___x_1667_);
                    if v___x_1668_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1644_ = 65;
                v___x_1645_ = lean_uint32_dec_le(v___x_1644_, v_c_1642_);
                if v___x_1645_ == 0 {
                    v___x_1646_ = 0;
                    return v___x_1646_;
                } else {
                    v___x_1647_ = 90;
                    v___x_1648_ = lean_uint32_dec_le(v_c_1642_, v___x_1647_);
                    if v___x_1648_ == 0 {
                        v___x_1649_ = 0;
                        return v___x_1649_;
                    } else {
                        v___x_1650_ = 1;
                        return v___x_1650_;
                    }
                }
            }
            2 => {
                if v___y_1652_ == 0 {
                    v___x_1653_ = 2;
                    return v___x_1653_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1655_ == 0 {
                    v___x_1656_ = 48;
                    v___x_1657_ = lean_uint32_dec_le(v___x_1656_, v_c_1642_);
                    if v___x_1657_ == 0 {
                        v___y_1652_ = v___x_1657_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1658_ = 57;
                        v___x_1659_ = lean_uint32_dec_le(v_c_1642_, v___x_1658_);
                        v___y_1652_ = v___x_1659_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_1661_ = 97;
                v___x_1662_ = lean_uint32_dec_le(v___x_1661_, v_c_1642_);
                if v___x_1662_ == 0 {
                    v___y_1655_ = v___x_1662_;
                    state = 3;
                    continue;
                } else {
                    v___x_1663_ = 122;
                    v___x_1664_ = lean_uint32_dec_le(v_c_1642_, v___x_1663_);
                    v___y_1655_ = v___x_1664_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FuzzyMatching_charType___boxed(
    mut v_c_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1670_: u32 = 0;
    let mut v_res_1671_: u8 = 0;
    let mut v_r_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1670_ = crate::leanh::lean_unbox_uint32(v_c_1669_);
    crate::leanh::lean_dec(v_c_1669_);
    v_res_1671_ = l_Lean_FuzzyMatching_charType(v_c_boxed_1670_);
    v_r_1672_ = crate::leanh::lean_box((v_res_1671_) as usize);
    return v_r_1672_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_ctorIdx(
    mut v_x_1673_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1673_ {
        0 => {
            let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1674_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1674_;
        }
        1 => {
            let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1675_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1675_;
        }
        _ => {
            let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1676_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1676_;
        }
    }
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_ctorIdx___boxed(
    mut v_x_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1678_: u8 = 0;
    let mut v_res_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1678_ = (crate::leanh::lean_unbox(v_x_1677_) as u8);
    v_res_1679_ = l_Lean_FuzzyMatching_CharRole_ctorIdx(v_x_boxed_1678_);
    return v_res_1679_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_toCtorIdx(
    mut v_x_1680_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = l_Lean_FuzzyMatching_CharRole_ctorIdx(v_x_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_toCtorIdx___boxed(
    mut v_x_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1683_: u8 = 0;
    let mut v_res_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1683_ = (crate::leanh::lean_unbox(v_x_1682_) as u8);
    v_res_1684_ = l_Lean_FuzzyMatching_CharRole_toCtorIdx(v_x_4__boxed_1683_);
    return v_res_1684_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(
    mut v_k_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1685_);
    return v_k_1685_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_ctorElim___redArg___boxed(
    mut v_k_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Lean_FuzzyMatching_CharRole_ctorElim___redArg(v_k_1686_);
    crate::leanh::lean_dec(v_k_1686_);
    return v_res_1687_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_ctorElim(
    mut v_motive_1688_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1689_: *mut crate::leanh::LeanObject,
    mut v_t_1690_: u8,
    mut v_h_1691_: *mut crate::leanh::LeanObject,
    mut v_k_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1692_);
    return v_k_1692_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_ctorElim___boxed(
    mut v_motive_1693_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1694_: *mut crate::leanh::LeanObject,
    mut v_t_1695_: *mut crate::leanh::LeanObject,
    mut v_h_1696_: *mut crate::leanh::LeanObject,
    mut v_k_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1698_: u8 = 0;
    let mut v_res_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1698_ = (crate::leanh::lean_unbox(v_t_1695_) as u8);
    v_res_1699_ = l_Lean_FuzzyMatching_CharRole_ctorElim(
        v_motive_1693_,
        v_ctorIdx_1694_,
        v_t_boxed_1698_,
        v_h_1696_,
        v_k_1697_,
    );
    crate::leanh::lean_dec(v_k_1697_);
    crate::leanh::lean_dec(v_ctorIdx_1694_);
    return v_res_1699_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_head_elim___redArg(
    mut v_head_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_head_1700_);
    return v_head_1700_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_head_elim___redArg___boxed(
    mut v_head_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lean_FuzzyMatching_CharRole_head_elim___redArg(v_head_1701_);
    crate::leanh::lean_dec(v_head_1701_);
    return v_res_1702_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_head_elim(
    mut v_motive_1703_: *mut crate::leanh::LeanObject,
    mut v_t_1704_: u8,
    mut v_h_1705_: *mut crate::leanh::LeanObject,
    mut v_head_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_head_1706_);
    return v_head_1706_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_head_elim___boxed(
    mut v_motive_1707_: *mut crate::leanh::LeanObject,
    mut v_t_1708_: *mut crate::leanh::LeanObject,
    mut v_h_1709_: *mut crate::leanh::LeanObject,
    mut v_head_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1711_: u8 = 0;
    let mut v_res_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1711_ = (crate::leanh::lean_unbox(v_t_1708_) as u8);
    v_res_1712_ = l_Lean_FuzzyMatching_CharRole_head_elim(
        v_motive_1707_,
        v_t_boxed_1711_,
        v_h_1709_,
        v_head_1710_,
    );
    crate::leanh::lean_dec(v_head_1710_);
    return v_res_1712_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(
    mut v_tail_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_tail_1713_);
    return v_tail_1713_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_tail_elim___redArg___boxed(
    mut v_tail_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1715_ = l_Lean_FuzzyMatching_CharRole_tail_elim___redArg(v_tail_1714_);
    crate::leanh::lean_dec(v_tail_1714_);
    return v_res_1715_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_tail_elim(
    mut v_motive_1716_: *mut crate::leanh::LeanObject,
    mut v_t_1717_: u8,
    mut v_h_1718_: *mut crate::leanh::LeanObject,
    mut v_tail_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_tail_1719_);
    return v_tail_1719_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_tail_elim___boxed(
    mut v_motive_1720_: *mut crate::leanh::LeanObject,
    mut v_t_1721_: *mut crate::leanh::LeanObject,
    mut v_h_1722_: *mut crate::leanh::LeanObject,
    mut v_tail_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1724_: u8 = 0;
    let mut v_res_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1724_ = (crate::leanh::lean_unbox(v_t_1721_) as u8);
    v_res_1725_ = l_Lean_FuzzyMatching_CharRole_tail_elim(
        v_motive_1720_,
        v_t_boxed_1724_,
        v_h_1722_,
        v_tail_1723_,
    );
    crate::leanh::lean_dec(v_tail_1723_);
    return v_res_1725_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(
    mut v_separator_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_separator_1726_);
    return v_separator_1726_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_separator_elim___redArg___boxed(
    mut v_separator_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1728_ = l_Lean_FuzzyMatching_CharRole_separator_elim___redArg(v_separator_1727_);
    crate::leanh::lean_dec(v_separator_1727_);
    return v_res_1728_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_separator_elim(
    mut v_motive_1729_: *mut crate::leanh::LeanObject,
    mut v_t_1730_: u8,
    mut v_h_1731_: *mut crate::leanh::LeanObject,
    mut v_separator_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_separator_1732_);
    return v_separator_1732_;
}
pub unsafe fn l_Lean_FuzzyMatching_CharRole_separator_elim___boxed(
    mut v_motive_1733_: *mut crate::leanh::LeanObject,
    mut v_t_1734_: *mut crate::leanh::LeanObject,
    mut v_h_1735_: *mut crate::leanh::LeanObject,
    mut v_separator_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1737_: u8 = 0;
    let mut v_res_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1737_ = (crate::leanh::lean_unbox(v_t_1734_) as u8);
    v_res_1738_ = l_Lean_FuzzyMatching_CharRole_separator_elim(
        v_motive_1733_,
        v_t_boxed_1737_,
        v_h_1735_,
        v_separator_1736_,
    );
    crate::leanh::lean_dec(v_separator_1736_);
    return v_res_1738_;
}
pub unsafe fn _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default() -> u8 {
    let mut v___x_1739_: u8 = 0;
    v___x_1739_ = 0;
    return v___x_1739_;
}
pub unsafe fn _init_l_Lean_FuzzyMatching_instInhabitedCharRole() -> u8 {
    let mut v___x_1740_: u8 = 0;
    v___x_1740_ = 0;
    return v___x_1740_;
}
pub unsafe fn l_Lean_FuzzyMatching_charRole(
    mut v_prev_x3f_1741_: *mut crate::leanh::LeanObject,
    mut v_curr_1742_: u8,
    mut v_next_x3f_1743_: *mut crate::leanh::LeanObject,
) -> u8 {
    if v_curr_1742_ == 2 {
        let mut v___x_1744_: u8 = 0;
        v___x_1744_ = 2;
        return v___x_1744_;
    } else {
        if crate::leanh::lean_obj_tag(v_prev_x3f_1741_) == 0 {
            let mut v___x_1745_: u8 = 0;
            v___x_1745_ = 0;
            return v___x_1745_;
        } else {
            let mut v_val_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1747_: u8 = 0;
            v_val_1746_ = crate::leanh::lean_ctor_get(v_prev_x3f_1741_, 0);
            v___x_1747_ = (crate::leanh::lean_unbox(v_val_1746_) as u8);
            if v___x_1747_ == 2 {
                let mut v___x_1748_: u8 = 0;
                v___x_1748_ = 0;
                return v___x_1748_;
            } else {
                if v_curr_1742_ == 0 {
                    let mut v___x_1749_: u8 = 0;
                    v___x_1749_ = 1;
                    return v___x_1749_;
                } else {
                    let mut v___x_1750_: u8 = 0;
                    v___x_1750_ = (crate::leanh::lean_unbox(v_val_1746_) as u8);
                    if v___x_1750_ == 1 {
                        if crate::leanh::lean_obj_tag(v_next_x3f_1743_) == 1 {
                            let mut v_val_1751_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1752_: u8 = 0;
                            v_val_1751_ = crate::leanh::lean_ctor_get(v_next_x3f_1743_, 0);
                            v___x_1752_ = (crate::leanh::lean_unbox(v_val_1751_) as u8);
                            if v___x_1752_ == 0 {
                                let mut v___x_1753_: u8 = 0;
                                v___x_1753_ = 0;
                                return v___x_1753_;
                            } else {
                                let mut v___x_1754_: u8 = 0;
                                v___x_1754_ = 1;
                                return v___x_1754_;
                            }
                        } else {
                            let mut v___x_1755_: u8 = 0;
                            v___x_1755_ = 1;
                            return v___x_1755_;
                        }
                    } else {
                        let mut v___x_1756_: u8 = 0;
                        v___x_1756_ = 0;
                        return v___x_1756_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_FuzzyMatching_charRole___boxed(
    mut v_prev_x3f_1757_: *mut crate::leanh::LeanObject,
    mut v_curr_1758_: *mut crate::leanh::LeanObject,
    mut v_next_x3f_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_curr_boxed_1760_: u8 = 0;
    let mut v_res_1761_: u8 = 0;
    let mut v_r_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_curr_boxed_1760_ = (crate::leanh::lean_unbox(v_curr_1758_) as u8);
    v_res_1761_ =
        l_Lean_FuzzyMatching_charRole(v_prev_x3f_1757_, v_curr_boxed_1760_, v_next_x3f_1759_);
    crate::leanh::lean_dec(v_next_x3f_1759_);
    crate::leanh::lean_dec(v_prev_x3f_1757_);
    v_r_1762_ = crate::leanh::lean_box((v_res_1761_) as usize);
    return v_r_1762_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(
    mut v_string_1763_: *mut crate::leanh::LeanObject,
    mut v_range_1764_: *mut crate::leanh::LeanObject,
    mut v_b_1765_: *mut crate::leanh::LeanObject,
    mut v_i_1766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1770_: u8 = 0;
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: u32 = 0;
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u32 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: u32 = 0;
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: u8 = 0;
    let mut v___x_1791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_1767_ = crate::leanh::lean_ctor_get(v_range_1764_, 1);
                v_step_1768_ = crate::leanh::lean_ctor_get(v_range_1764_, 2);
                v___x_1775_ = lean_nat_dec_lt(v_i_1766_, v_stop_1767_);
                if v___x_1775_ == 0 {
                    crate::leanh::lean_dec(v_i_1766_);
                    return v_b_1765_;
                } else {
                    v___x_1776_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1777_ = lean_nat_sub(v_i_1766_, v___x_1776_);
                    v___x_1778_ = lean_string_utf8_get(v_string_1763_, v___x_1777_);
                    crate::leanh::lean_dec(v___x_1777_);
                    v___x_1779_ = l_Lean_FuzzyMatching_charType(v___x_1778_);
                    if v___x_1779_ == 2 {
                        v___x_1780_ = 2;
                        v___y_1770_ = v___x_1780_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1781_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1782_ = lean_nat_sub(v_i_1766_, v___x_1781_);
                        v___x_1783_ = lean_string_utf8_get(v_string_1763_, v___x_1782_);
                        crate::leanh::lean_dec(v___x_1782_);
                        v___x_1784_ = l_Lean_FuzzyMatching_charType(v___x_1783_);
                        if v___x_1784_ == 2 {
                            v___x_1785_ = 0;
                            v___y_1770_ = v___x_1785_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_1779_ == 0 {
                                v___x_1786_ = 1;
                                v___y_1770_ = v___x_1786_;
                                state = 1;
                                continue;
                            } else {
                                if v___x_1784_ == 1 {
                                    v___x_1787_ = lean_string_utf8_get(v_string_1763_, v_i_1766_);
                                    v___x_1788_ = l_Lean_FuzzyMatching_charType(v___x_1787_);
                                    if v___x_1788_ == 0 {
                                        v___x_1789_ = 0;
                                        v___y_1770_ = v___x_1789_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1790_ = 1;
                                        v___y_1770_ = v___x_1790_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___x_1791_ = 0;
                                    v___y_1770_ = v___x_1791_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1771_ = crate::leanh::lean_box((v___y_1770_) as usize);
                v___x_1772_ = lean_array_push(v_b_1765_, v___x_1771_);
                v___x_1773_ = lean_nat_add(v_i_1766_, v_step_1768_);
                crate::leanh::lean_dec(v_i_1766_);
                v_b_1765_ = v___x_1772_;
                v_i_1766_ = v___x_1773_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_string_1792_: *mut crate::leanh::LeanObject,
    mut v_range_1793_: *mut crate::leanh::LeanObject,
    mut v_b_1794_: *mut crate::leanh::LeanObject,
    mut v_i_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1796_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_1792_, v_range_1793_, v_b_1794_, v_i_1795_);
    crate::leanh::lean_dec_ref(v_range_1793_);
    crate::leanh::lean_dec_ref(v_string_1792_);
    return v_res_1796_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(
    mut v_string_1797_: *mut crate::leanh::LeanObject,
    mut v_range_1798_: *mut crate::leanh::LeanObject,
    mut v_b_1799_: *mut crate::leanh::LeanObject,
    mut v_i_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u32 = 0;
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: u8 = 0;
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u32 = 0;
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1821_: u32 = 0;
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_1801_ = crate::leanh::lean_ctor_get(v_range_1798_, 1);
                v_step_1802_ = crate::leanh::lean_ctor_get(v_range_1798_, 2);
                v___x_1809_ = lean_nat_dec_lt(v_i_1800_, v_stop_1801_);
                if v___x_1809_ == 0 {
                    return v_b_1799_;
                } else {
                    v___x_1810_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1811_ = lean_nat_sub(v_i_1800_, v___x_1810_);
                    v___x_1812_ = lean_string_utf8_get(v_string_1797_, v___x_1811_);
                    crate::leanh::lean_dec(v___x_1811_);
                    v___x_1813_ = l_Lean_FuzzyMatching_charType(v___x_1812_);
                    if v___x_1813_ == 2 {
                        v___x_1814_ = 2;
                        v___y_1804_ = v___x_1814_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1815_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1816_ = lean_nat_sub(v_i_1800_, v___x_1815_);
                        v___x_1817_ = lean_string_utf8_get(v_string_1797_, v___x_1816_);
                        crate::leanh::lean_dec(v___x_1816_);
                        v___x_1818_ = l_Lean_FuzzyMatching_charType(v___x_1817_);
                        if v___x_1818_ == 2 {
                            v___x_1819_ = 0;
                            v___y_1804_ = v___x_1819_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_1813_ == 0 {
                                v___x_1820_ = 1;
                                v___y_1804_ = v___x_1820_;
                                state = 1;
                                continue;
                            } else {
                                if v___x_1818_ == 1 {
                                    v___x_1821_ = lean_string_utf8_get(v_string_1797_, v_i_1800_);
                                    v___x_1822_ = l_Lean_FuzzyMatching_charType(v___x_1821_);
                                    if v___x_1822_ == 0 {
                                        v___x_1823_ = 0;
                                        v___y_1804_ = v___x_1823_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1824_ = 1;
                                        v___y_1804_ = v___x_1824_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___x_1825_ = 0;
                                    v___y_1804_ = v___x_1825_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1805_ = crate::leanh::lean_box((v___y_1804_) as usize);
                v___x_1806_ = lean_array_push(v_b_1799_, v___x_1805_);
                v___x_1807_ = lean_nat_add(v_i_1800_, v_step_1802_);
                v___x_1808_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_1797_, v_range_1798_, v___x_1806_, v___x_1807_);
                return v___x_1808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg___boxed(
    mut v_string_1826_: *mut crate::leanh::LeanObject,
    mut v_range_1827_: *mut crate::leanh::LeanObject,
    mut v_b_1828_: *mut crate::leanh::LeanObject,
    mut v_i_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1830_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_1826_, v_range_1827_, v_b_1828_, v_i_1829_);
    crate::leanh::lean_dec(v_i_1829_);
    crate::leanh::lean_dec_ref(v_range_1827_);
    crate::leanh::lean_dec_ref(v_string_1826_);
    return v_res_1830_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(
    mut v_prev_x3f_1831_: *mut crate::leanh::LeanObject,
    mut v_curr_1832_: u32,
    mut v_next_x3f_1833_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1836_: u8 = 0;
    let mut v___y_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: u8 = 0;
    let mut v___x_1839_: u8 = 0;
    let mut v_val_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: u8 = 0;
    let mut v___x_1844_: u8 = 0;
    let mut v_val_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: u8 = 0;
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: u8 = 0;
    let mut v___y_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1859_: u32 = 0;
    let mut v___x_1860_: u8 = 0;
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1865_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1870_: u8 = 0;
    let mut v___x_1871_: u32 = 0;
    let mut v___x_1872_: u8 = 0;
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_prev_x3f_1831_) == 0 {
                    v___x_1866_ = crate::leanh::lean_box(0);
                    v___y_1852_ = v___x_1866_;
                    state = 2;
                    continue;
                } else {
                    v_val_1867_ = crate::leanh::lean_ctor_get(v_prev_x3f_1831_, 0);
                    v_isSharedCheck_1877_ =
                        (!crate::leanh::lean_is_exclusive(v_prev_x3f_1831_)) as u8;
                    if v_isSharedCheck_1877_ == 0 {
                        v___x_1869_ = v_prev_x3f_1831_;
                        v_isShared_1870_ = v_isSharedCheck_1877_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1867_);
                        crate::leanh::lean_dec(v_prev_x3f_1831_);
                        v___x_1869_ = crate::leanh::lean_box(0);
                        v_isShared_1870_ = v_isSharedCheck_1877_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1836_ == 2 {
                    crate::leanh::lean_dec(v___y_1837_);
                    crate::leanh::lean_dec(v___y_1835_);
                    v___x_1838_ = 2;
                    return v___x_1838_;
                } else {
                    if crate::leanh::lean_obj_tag(v___y_1835_) == 0 {
                        crate::leanh::lean_dec(v___y_1837_);
                        v___x_1839_ = 0;
                        return v___x_1839_;
                    } else {
                        v_val_1840_ = crate::leanh::lean_ctor_get(v___y_1835_, 0);
                        crate::leanh::lean_inc(v_val_1840_);
                        crate::leanh::lean_dec_ref_known(v___y_1835_, 1);
                        v___x_1841_ = (crate::leanh::lean_unbox(v_val_1840_) as u8);
                        if v___x_1841_ == 2 {
                            crate::leanh::lean_dec(v_val_1840_);
                            crate::leanh::lean_dec(v___y_1837_);
                            v___x_1842_ = 0;
                            return v___x_1842_;
                        } else {
                            if v___y_1836_ == 0 {
                                crate::leanh::lean_dec(v_val_1840_);
                                crate::leanh::lean_dec(v___y_1837_);
                                v___x_1843_ = 1;
                                return v___x_1843_;
                            } else {
                                v___x_1844_ = (crate::leanh::lean_unbox(v_val_1840_) as u8);
                                crate::leanh::lean_dec(v_val_1840_);
                                if v___x_1844_ == 1 {
                                    if crate::leanh::lean_obj_tag(v___y_1837_) == 1 {
                                        v_val_1845_ = crate::leanh::lean_ctor_get(v___y_1837_, 0);
                                        crate::leanh::lean_inc(v_val_1845_);
                                        crate::leanh::lean_dec_ref_known(v___y_1837_, 1);
                                        v___x_1846_ = (crate::leanh::lean_unbox(v_val_1845_) as u8);
                                        crate::leanh::lean_dec(v_val_1845_);
                                        if v___x_1846_ == 0 {
                                            v___x_1847_ = 0;
                                            return v___x_1847_;
                                        } else {
                                            v___x_1848_ = 1;
                                            return v___x_1848_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___y_1837_);
                                        v___x_1849_ = 1;
                                        return v___x_1849_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___y_1837_);
                                    v___x_1850_ = 0;
                                    return v___x_1850_;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1853_ = l_Lean_FuzzyMatching_charType(v_curr_1832_);
                if crate::leanh::lean_obj_tag(v_next_x3f_1833_) == 0 {
                    v___x_1854_ = crate::leanh::lean_box(0);
                    v___y_1835_ = v___y_1852_;
                    v___y_1836_ = v___x_1853_;
                    v___y_1837_ = v___x_1854_;
                    state = 1;
                    continue;
                } else {
                    v_val_1855_ = crate::leanh::lean_ctor_get(v_next_x3f_1833_, 0);
                    v_isSharedCheck_1865_ =
                        (!crate::leanh::lean_is_exclusive(v_next_x3f_1833_)) as u8;
                    if v_isSharedCheck_1865_ == 0 {
                        v___x_1857_ = v_next_x3f_1833_;
                        v_isShared_1858_ = v_isSharedCheck_1865_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1855_);
                        crate::leanh::lean_dec(v_next_x3f_1833_);
                        v___x_1857_ = crate::leanh::lean_box(0);
                        v_isShared_1858_ = v_isSharedCheck_1865_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1859_ = crate::leanh::lean_unbox_uint32(v_val_1855_);
                crate::leanh::lean_dec(v_val_1855_);
                v___x_1860_ = l_Lean_FuzzyMatching_charType(v___x_1859_);
                v___x_1861_ = crate::leanh::lean_box((v___x_1860_) as usize);
                if v_isShared_1858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1861_);
                    v___x_1863_ = v___x_1857_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
                    v___x_1863_ = v_reuseFailAlloc_1864_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_1835_ = v___y_1852_;
                v___y_1836_ = v___x_1853_;
                v___y_1837_ = v___x_1863_;
                state = 1;
                continue;
            }
            5 => {
                v___x_1871_ = crate::leanh::lean_unbox_uint32(v_val_1867_);
                crate::leanh::lean_dec(v_val_1867_);
                v___x_1872_ = l_Lean_FuzzyMatching_charType(v___x_1871_);
                v___x_1873_ = crate::leanh::lean_box((v___x_1872_) as usize);
                if v_isShared_1870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1869_, 0, v___x_1873_);
                    v___x_1875_ = v___x_1869_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1876_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
                    v___x_1875_ = v_reuseFailAlloc_1876_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_1852_ = v___x_1875_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0___boxed(
    mut v_prev_x3f_1878_: *mut crate::leanh::LeanObject,
    mut v_curr_1879_: *mut crate::leanh::LeanObject,
    mut v_next_x3f_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_curr_boxed_1881_: u32 = 0;
    let mut v_res_1882_: u8 = 0;
    let mut v_r_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_curr_boxed_1881_ = crate::leanh::lean_unbox_uint32(v_curr_1879_);
    crate::leanh::lean_dec(v_curr_1879_);
    v_res_1882_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v_prev_x3f_1878_, v_curr_boxed_1881_, v_next_x3f_1880_);
    v_r_1883_ = crate::leanh::lean_box((v_res_1882_) as usize);
    return v_r_1883_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(
    mut v_string_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: u8 = 0;
    v___x_1887_ = lean_string_utf8_byte_size(v_string_1886_);
    v___x_1888_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1889_ = lean_nat_dec_eq(v___x_1887_, v___x_1888_);
    if v___x_1889_ == 0 {
        let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: u8 = 0;
        v___x_1890_ = lean_string_length(v_string_1886_);
        v___x_1891_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1892_ = lean_nat_dec_eq(v___x_1890_, v___x_1891_);
        if v___x_1892_ == 0 {
            let mut v_result_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1895_: u32 = 0;
            let mut v___x_1896_: u32 = 0;
            let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1899_: u8 = 0;
            let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_result_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1906_: u32 = 0;
            let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1910_: u32 = 0;
            let mut v___x_1911_: u8 = 0;
            let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_result_1893_ = lean_mk_empty_array_with_capacity(v___x_1890_);
            v___x_1894_ = crate::leanh::lean_box(0);
            v___x_1895_ = lean_string_utf8_get(v_string_1886_, v___x_1888_);
            v___x_1896_ = lean_string_utf8_get(v_string_1886_, v___x_1891_);
            v___x_1897_ = crate::leanh::lean_box_uint32(v___x_1896_);
            v___x_1898_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1898_, 0, v___x_1897_);
            v___x_1899_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_1894_, v___x_1895_, v___x_1898_);
            v___x_1900_ = crate::leanh::lean_box((v___x_1899_) as usize);
            v_result_1901_ = lean_array_push(v_result_1893_, v___x_1900_);
            v___x_1902_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_1903_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1903_, 0, v___x_1902_);
            crate::leanh::lean_ctor_set(v___x_1903_, 1, v___x_1890_);
            crate::leanh::lean_ctor_set(v___x_1903_, 2, v___x_1891_);
            v___x_1904_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_1886_, v___x_1903_, v_result_1901_, v___x_1902_);
            crate::leanh::lean_dec_ref_known(v___x_1903_, 3);
            v___x_1905_ = lean_nat_sub(v___x_1890_, v___x_1902_);
            v___x_1906_ = lean_string_utf8_get(v_string_1886_, v___x_1905_);
            crate::leanh::lean_dec(v___x_1905_);
            v___x_1907_ = crate::leanh::lean_box_uint32(v___x_1906_);
            v___x_1908_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1908_, 0, v___x_1907_);
            v___x_1909_ = lean_nat_sub(v___x_1890_, v___x_1891_);
            v___x_1910_ = lean_string_utf8_get(v_string_1886_, v___x_1909_);
            crate::leanh::lean_dec(v___x_1909_);
            v___x_1911_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_1908_, v___x_1910_, v___x_1894_);
            v___x_1912_ = crate::leanh::lean_box((v___x_1911_) as usize);
            v___x_1913_ = lean_array_push(v___x_1904_, v___x_1912_);
            return v___x_1913_;
        } else {
            let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1915_: u32 = 0;
            let mut v___x_1916_: u8 = 0;
            let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1914_ = crate::leanh::lean_box(0);
            v___x_1915_ = lean_string_utf8_get(v_string_1886_, v___x_1888_);
            v___x_1916_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___lam__0(v___x_1914_, v___x_1915_, v___x_1914_);
            v___x_1917_ = lean_mk_empty_array_with_capacity(v___x_1891_);
            v___x_1918_ = crate::leanh::lean_box((v___x_1916_) as usize);
            v___x_1919_ = lean_array_push(v___x_1917_, v___x_1918_);
            return v___x_1919_;
        }
    } else {
        let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1920_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___closed__0;
        return v___x_1920_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0___boxed(
    mut v_string_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_string_1921_);
    crate::leanh::lean_dec_ref(v_string_1921_);
    return v_res_1922_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(
    mut v_s_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_s_1923_);
    return v___x_1924_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo___boxed(
    mut v_s_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1926_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo(v_s_1925_);
    crate::leanh::lean_dec_ref(v_s_1925_);
    return v_res_1926_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(
    mut v_string_1927_: *mut crate::leanh::LeanObject,
    mut v_range_1928_: *mut crate::leanh::LeanObject,
    mut v_b_1929_: *mut crate::leanh::LeanObject,
    mut v_i_1930_: *mut crate::leanh::LeanObject,
    mut v_hs_1931_: *mut crate::leanh::LeanObject,
    mut v_hl_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1933_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___redArg(v_string_1927_, v_range_1928_, v_b_1929_, v_i_1930_);
    return v___x_1933_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0___boxed(
    mut v_string_1934_: *mut crate::leanh::LeanObject,
    mut v_range_1935_: *mut crate::leanh::LeanObject,
    mut v_b_1936_: *mut crate::leanh::LeanObject,
    mut v_i_1937_: *mut crate::leanh::LeanObject,
    mut v_hs_1938_: *mut crate::leanh::LeanObject,
    mut v_hl_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1940_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0(v_string_1934_, v_range_1935_, v_b_1936_, v_i_1937_, v_hs_1938_, v_hl_1939_);
    crate::leanh::lean_dec(v_i_1937_);
    crate::leanh::lean_dec_ref(v_range_1935_);
    crate::leanh::lean_dec_ref(v_string_1934_);
    return v_res_1940_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(
    mut v_string_1941_: *mut crate::leanh::LeanObject,
    mut v_range_1942_: *mut crate::leanh::LeanObject,
    mut v_b_1943_: *mut crate::leanh::LeanObject,
    mut v_i_1944_: *mut crate::leanh::LeanObject,
    mut v_hs_1945_: *mut crate::leanh::LeanObject,
    mut v_hl_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1947_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___redArg(v_string_1941_, v_range_1942_, v_b_1943_, v_i_1944_);
    return v___x_1947_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1___boxed(
    mut v_string_1948_: *mut crate::leanh::LeanObject,
    mut v_range_1949_: *mut crate::leanh::LeanObject,
    mut v_b_1950_: *mut crate::leanh::LeanObject,
    mut v_i_1951_: *mut crate::leanh::LeanObject,
    mut v_hs_1952_: *mut crate::leanh::LeanObject,
    mut v_hl_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1954_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0_spec__0_spec__1(v_string_1948_, v_range_1949_, v_b_1950_, v_i_1951_, v_hs_1952_, v_hl_1953_);
    crate::leanh::lean_dec_ref(v_range_1949_);
    crate::leanh::lean_dec_ref(v_string_1948_);
    return v_res_1954_;
}
pub unsafe fn _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0() -> u16 {
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u16 = 0;
    v___x_1955_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1956_ = lean_int16_of_nat(v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn _init_l_Lean_FuzzyMatching_instInhabitedScore_default() -> u16 {
    let mut v___x_1957_: u16 = 0;
    v___x_1957_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once),
        _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0,
    );
    return v___x_1957_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore()
-> u16 {
    let mut v___x_1958_: u16 = 0;
    v___x_1958_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
    return v___x_1958_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0()
-> u16 {
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u16 = 0;
    v___x_1959_ = crate::leanh::lean_unsigned_to_nat(32768);
    v___x_1960_ = lean_int16_of_nat(v___x_1959_);
    return v___x_1960_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1()
-> u16 {
    let mut v___x_1961_: u16 = 0;
    let mut v___x_1962_: u16 = 0;
    v___x_1961_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0_once
        ),
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__0,
    );
    v___x_1962_ = lean_int16_neg(v___x_1961_);
    return v___x_1962_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful() -> u16 {
    let mut v___x_1963_: u16 = 0;
    v___x_1963_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once
        ),
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1,
    );
    return v___x_1963_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(
    mut v_x_1964_: u16,
) -> u8 {
    let mut v___x_1965_: u16 = 0;
    let mut v___x_1966_: u8 = 0;
    v___x_1965_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once
        ),
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1,
    );
    v___x_1966_ = lean_int16_dec_le(v_x_1964_, v___x_1965_);
    return v___x_1966_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful___boxed(
    mut v_x_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1968_: u16 = 0;
    let mut v_res_1969_: u8 = 0;
    let mut v_r_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1968_ = (crate::leanh::lean_unbox(v_x_1967_) as u16);
    v_res_1969_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_isAwful(v_x_boxed_1968_);
    v_r_1970_ = crate::leanh::lean_box((v_res_1969_) as usize);
    return v_r_1970_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(
    mut v_x_1971_: u16,
    mut v_f_1972_: *mut crate::leanh::LeanObject,
) -> u16 {
    let mut v___x_1973_: u16 = 0;
    let mut v___x_1974_: u8 = 0;
    v___x_1973_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once
        ),
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1,
    );
    v___x_1974_ = lean_int16_dec_le(v_x_1971_, v___x_1973_);
    if v___x_1974_ == 0 {
        let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1977_: u16 = 0;
        v___x_1975_ = crate::leanh::lean_box((v_x_1971_) as usize);
        v___x_1976_ = crate::leanh::lean_apply_1(v_f_1972_, v___x_1975_);
        v___x_1977_ = (crate::leanh::lean_unbox(v___x_1976_) as u16);
        return v___x_1977_;
    } else {
        crate::leanh::lean_dec_ref(v_f_1972_);
        return v_x_1971_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___boxed(
    mut v_x_1978_: *mut crate::leanh::LeanObject,
    mut v_f_1979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1980_: u16 = 0;
    let mut v_res_1981_: u16 = 0;
    let mut v_r_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1980_ = (crate::leanh::lean_unbox(v_x_1978_) as u16);
    v_res_1981_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map(
        v_x_boxed_1980_,
        v_f_1979_,
    );
    v_r_1982_ = crate::leanh::lean_box((v_res_1981_) as usize);
    return v_r_1982_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(
    mut v_x_1983_: u16,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1984_: u16 = 0;
    let mut v___x_1985_: u8 = 0;
    v___x_1984_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once
        ),
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1,
    );
    v___x_1985_ = lean_int16_dec_le(v_x_1983_, v___x_1984_);
    if v___x_1985_ == 0 {
        let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1986_ = crate::leanh::lean_box((v_x_1983_) as usize);
        v___x_1987_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1987_, 0, v___x_1986_);
        return v___x_1987_;
    } else {
        let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1988_ = crate::leanh::lean_box(0);
        return v___x_1988_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f___boxed(
    mut v_x_1989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1990_: u16 = 0;
    let mut v_res_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1990_ = (crate::leanh::lean_unbox(v_x_1989_) as u16);
    v_res_1991_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt16_x3f(
        v_x_boxed_1990_,
    );
    return v_res_1991_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(
    mut v_x_1992_: u16,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1993_: u16 = 0;
    let mut v___x_1994_: u8 = 0;
    v___x_1993_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once
        ),
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1,
    );
    v___x_1994_ = lean_int16_dec_le(v_x_1992_, v___x_1993_);
    if v___x_1994_ == 0 {
        let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1995_ = lean_int16_to_int(v_x_1992_);
        v___x_1996_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1996_, 0, v___x_1995_);
        return v___x_1996_;
    } else {
        let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1997_ = crate::leanh::lean_box(0);
        return v___x_1997_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f___boxed(
    mut v_x_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1999_: u16 = 0;
    let mut v_res_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1999_ = (crate::leanh::lean_unbox(v_x_1998_) as u16);
    v_res_2000_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_toInt_x3f(v_x_boxed_1999_);
    return v_res_2000_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__2;
    v___x_2005_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2006_ = crate::leanh::lean_unsigned_to_nat(124);
    v___x_2007_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__1;
    v___x_2008_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__0;
    v___x_2009_ = l_mkPanicMessageWithDecl(
        v___x_2008_,
        v___x_2007_,
        v___x_2006_,
        v___x_2005_,
        v___x_2004_,
    );
    return v___x_2009_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(
    mut v_x_2010_: u16,
) -> u16 {
    let mut v___x_2011_: u16 = 0;
    let mut v___x_2012_: u8 = 0;
    v___x_2011_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once
        ),
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1,
    );
    v___x_2012_ = lean_int16_dec_eq(v_x_2010_, v___x_2011_);
    if v___x_2012_ == 0 {
        return v_x_2010_;
    } else {
        let mut v___x_2013_: u16 = 0;
        let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2017_: u16 = 0;
        v___x_2013_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
        v___x_2014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
        v___x_2015_ = crate::leanh::lean_box((v___x_2013_) as usize);
        v___x_2016_ = l_panic___redArg(v___x_2015_, v___x_2014_);
        crate::leanh::lean_dec(v___x_2015_);
        v___x_2017_ = (crate::leanh::lean_unbox(v___x_2016_) as u16);
        crate::leanh::lean_dec(v___x_2016_);
        return v___x_2017_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___boxed(
    mut v_x_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2019_: u16 = 0;
    let mut v_res_2020_: u16 = 0;
    let mut v_r_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2019_ = (crate::leanh::lean_unbox(v_x_2018_) as u16);
    v_res_2020_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21(
        v_x_boxed_2019_,
    );
    v_r_2021_ = crate::leanh::lean_box((v_res_2020_) as usize);
    return v_r_2021_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(
    mut v_missScore_2022_: u16,
    mut v_matchScore_2023_: u16,
) -> u16 {
    let mut v___x_2024_: u8 = 0;
    v___x_2024_ = lean_int16_dec_le(v_missScore_2022_, v_matchScore_2023_);
    if v___x_2024_ == 0 {
        return v_missScore_2022_;
    } else {
        return v_matchScore_2023_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest___boxed(
    mut v_missScore_2025_: *mut crate::leanh::LeanObject,
    mut v_matchScore_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_missScore_boxed_2027_: u16 = 0;
    let mut v_matchScore_boxed_2028_: u16 = 0;
    let mut v_res_2029_: u16 = 0;
    let mut v_r_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_missScore_boxed_2027_ = (crate::leanh::lean_unbox(v_missScore_2025_) as u16);
    v_matchScore_boxed_2028_ = (crate::leanh::lean_unbox(v_matchScore_2026_) as u16);
    v_res_2029_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_selectBest(
        v_missScore_boxed_2027_,
        v_matchScore_boxed_2028_,
    );
    v_r_2030_ = crate::leanh::lean_box((v_res_2029_) as usize);
    return v_r_2030_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(
    mut v_word_2031_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2032_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = lean_string_length(v_word_2031_);
    v___x_2035_ = lean_nat_mul(v_patternIdx_2032_, v___x_2034_);
    v___x_2036_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2037_ = lean_nat_mul(v___x_2035_, v___x_2036_);
    crate::leanh::lean_dec(v___x_2035_);
    v___x_2038_ = lean_nat_mul(v_wordIdx_2033_, v___x_2036_);
    v___x_2039_ = lean_nat_add(v___x_2037_, v___x_2038_);
    crate::leanh::lean_dec(v___x_2038_);
    crate::leanh::lean_dec(v___x_2037_);
    return v___x_2039_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx___boxed(
    mut v_word_2040_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2041_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2043_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getDoubleIdx(
            v_word_2040_,
            v_patternIdx_2041_,
            v_wordIdx_2042_,
        );
    crate::leanh::lean_dec(v_wordIdx_2042_);
    crate::leanh::lean_dec(v_patternIdx_2041_);
    crate::leanh::lean_dec_ref(v_word_2040_);
    return v_res_2043_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(
    mut v_word_2044_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2045_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2047_ = lean_string_length(v_word_2044_);
    v___x_2048_ = lean_nat_mul(v_patternIdx_2045_, v___x_2047_);
    v___x_2049_ = lean_nat_add(v___x_2048_, v_wordIdx_2046_);
    crate::leanh::lean_dec(v___x_2048_);
    return v___x_2049_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx___boxed(
    mut v_word_2050_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2051_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2053_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getIdx(
        v_word_2050_,
        v_patternIdx_2051_,
        v_wordIdx_2052_,
    );
    crate::leanh::lean_dec(v_wordIdx_2052_);
    crate::leanh::lean_dec(v_patternIdx_2051_);
    crate::leanh::lean_dec_ref(v_word_2050_);
    return v_res_2053_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(
    mut v_word_2054_: *mut crate::leanh::LeanObject,
    mut v_result_2055_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2056_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2057_: *mut crate::leanh::LeanObject,
) -> u16 {
    let mut v___x_2058_: u16 = 0;
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u16 = 0;
    v___x_2058_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
    v___x_2059_ = lean_string_length(v_word_2054_);
    v___x_2060_ = lean_nat_mul(v_patternIdx_2056_, v___x_2059_);
    v___x_2061_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2062_ = lean_nat_mul(v___x_2060_, v___x_2061_);
    crate::leanh::lean_dec(v___x_2060_);
    v___x_2063_ = lean_nat_mul(v_wordIdx_2057_, v___x_2061_);
    v___x_2064_ = lean_nat_add(v___x_2062_, v___x_2063_);
    crate::leanh::lean_dec(v___x_2063_);
    crate::leanh::lean_dec(v___x_2062_);
    v___x_2065_ = crate::leanh::lean_box((v___x_2058_) as usize);
    v___x_2066_ = lean_array_get(v___x_2065_, v_result_2055_, v___x_2064_);
    crate::leanh::lean_dec(v___x_2064_);
    crate::leanh::lean_dec(v___x_2065_);
    v___x_2067_ = (crate::leanh::lean_unbox(v___x_2066_) as u16);
    crate::leanh::lean_dec(v___x_2066_);
    return v___x_2067_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss___boxed(
    mut v_word_2068_: *mut crate::leanh::LeanObject,
    mut v_result_2069_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2070_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2072_: u16 = 0;
    let mut v_r_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2072_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMiss(
        v_word_2068_,
        v_result_2069_,
        v_patternIdx_2070_,
        v_wordIdx_2071_,
    );
    crate::leanh::lean_dec(v_wordIdx_2071_);
    crate::leanh::lean_dec(v_patternIdx_2070_);
    crate::leanh::lean_dec_ref(v_result_2069_);
    crate::leanh::lean_dec_ref(v_word_2068_);
    v_r_2073_ = crate::leanh::lean_box((v_res_2072_) as usize);
    return v_r_2073_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(
    mut v_word_2074_: *mut crate::leanh::LeanObject,
    mut v_result_2075_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2076_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2077_: *mut crate::leanh::LeanObject,
) -> u16 {
    let mut v___x_2078_: u16 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: u16 = 0;
    v___x_2078_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
    v___x_2079_ = lean_string_length(v_word_2074_);
    v___x_2080_ = lean_nat_mul(v_patternIdx_2076_, v___x_2079_);
    v___x_2081_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2082_ = lean_nat_mul(v___x_2080_, v___x_2081_);
    crate::leanh::lean_dec(v___x_2080_);
    v___x_2083_ = lean_nat_mul(v_wordIdx_2077_, v___x_2081_);
    v___x_2084_ = lean_nat_add(v___x_2082_, v___x_2083_);
    crate::leanh::lean_dec(v___x_2083_);
    crate::leanh::lean_dec(v___x_2082_);
    v___x_2085_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2086_ = lean_nat_add(v___x_2084_, v___x_2085_);
    crate::leanh::lean_dec(v___x_2084_);
    v___x_2087_ = crate::leanh::lean_box((v___x_2078_) as usize);
    v___x_2088_ = lean_array_get(v___x_2087_, v_result_2075_, v___x_2086_);
    crate::leanh::lean_dec(v___x_2086_);
    crate::leanh::lean_dec(v___x_2087_);
    v___x_2089_ = (crate::leanh::lean_unbox(v___x_2088_) as u16);
    crate::leanh::lean_dec(v___x_2088_);
    return v___x_2089_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch___boxed(
    mut v_word_2090_: *mut crate::leanh::LeanObject,
    mut v_result_2091_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2092_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2094_: u16 = 0;
    let mut v_r_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2094_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_getMatch(
        v_word_2090_,
        v_result_2091_,
        v_patternIdx_2092_,
        v_wordIdx_2093_,
    );
    crate::leanh::lean_dec(v_wordIdx_2093_);
    crate::leanh::lean_dec(v_patternIdx_2092_);
    crate::leanh::lean_dec_ref(v_result_2091_);
    crate::leanh::lean_dec_ref(v_word_2090_);
    v_r_2095_ = crate::leanh::lean_box((v_res_2094_) as usize);
    return v_r_2095_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(
    mut v_word_2096_: *mut crate::leanh::LeanObject,
    mut v_result_2097_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2098_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2099_: *mut crate::leanh::LeanObject,
    mut v_missValue_2100_: u16,
    mut v_matchValue_2101_: u16,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2102_ = lean_string_length(v_word_2096_);
    v___x_2103_ = lean_nat_mul(v_patternIdx_2098_, v___x_2102_);
    v___x_2104_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2105_ = lean_nat_mul(v___x_2103_, v___x_2104_);
    crate::leanh::lean_dec(v___x_2103_);
    v___x_2106_ = lean_nat_mul(v_wordIdx_2099_, v___x_2104_);
    v_idx_2107_ = lean_nat_add(v___x_2105_, v___x_2106_);
    crate::leanh::lean_dec(v___x_2106_);
    crate::leanh::lean_dec(v___x_2105_);
    v___x_2108_ = crate::leanh::lean_box((v_missValue_2100_) as usize);
    v___x_2109_ = lean_array_set(v_result_2097_, v_idx_2107_, v___x_2108_);
    v___x_2110_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2111_ = lean_nat_add(v_idx_2107_, v___x_2110_);
    crate::leanh::lean_dec(v_idx_2107_);
    v___x_2112_ = crate::leanh::lean_box((v_matchValue_2101_) as usize);
    v___x_2113_ = lean_array_set(v___x_2109_, v___x_2111_, v___x_2112_);
    crate::leanh::lean_dec(v___x_2111_);
    return v___x_2113_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set___boxed(
    mut v_word_2114_: *mut crate::leanh::LeanObject,
    mut v_result_2115_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2116_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2117_: *mut crate::leanh::LeanObject,
    mut v_missValue_2118_: *mut crate::leanh::LeanObject,
    mut v_matchValue_2119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_missValue_boxed_2120_: u16 = 0;
    let mut v_matchValue_boxed_2121_: u16 = 0;
    let mut v_res_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_missValue_boxed_2120_ = (crate::leanh::lean_unbox(v_missValue_2118_) as u16);
    v_matchValue_boxed_2121_ = (crate::leanh::lean_unbox(v_matchValue_2119_) as u16);
    v_res_2122_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_set(
        v_word_2114_,
        v_result_2115_,
        v_patternIdx_2116_,
        v_wordIdx_2117_,
        v_missValue_boxed_2120_,
        v_matchValue_boxed_2121_,
    );
    crate::leanh::lean_dec(v_wordIdx_2117_);
    crate::leanh::lean_dec(v_patternIdx_2116_);
    crate::leanh::lean_dec_ref(v_word_2114_);
    return v_res_2122_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0()
-> u16 {
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: u16 = 0;
    v___x_2123_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2124_ = lean_int16_of_nat(v___x_2123_);
    return v___x_2124_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1()
-> u16 {
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u16 = 0;
    v___x_2125_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2126_ = lean_int16_of_nat(v___x_2125_);
    return v___x_2126_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(
    mut v_wordRole_2127_: u8,
    mut v_wordStart_2128_: u8,
) -> u16 {
    if v_wordStart_2128_ == 0 {
        if v_wordRole_2127_ == 0 {
            let mut v___x_2129_: u16 = 0;
            v___x_2129_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
            return v___x_2129_;
        } else {
            let mut v___x_2130_: u16 = 0;
            v___x_2130_ = crate::leanh::lean_uint16_once(
                core::ptr::addr_of_mut!(
                    l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once
                ),
                _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0,
            );
            return v___x_2130_;
        }
    } else {
        let mut v___x_2131_: u16 = 0;
        v___x_2131_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
        return v___x_2131_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___boxed(
    mut v_wordRole_2132_: *mut crate::leanh::LeanObject,
    mut v_wordStart_2133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_wordRole_boxed_2134_: u8 = 0;
    let mut v_wordStart_boxed_2135_: u8 = 0;
    let mut v_res_2136_: u16 = 0;
    let mut v_r_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_wordRole_boxed_2134_ = (crate::leanh::lean_unbox(v_wordRole_2132_) as u8);
    v_wordStart_boxed_2135_ = (crate::leanh::lean_unbox(v_wordStart_2133_) as u8);
    v_res_2136_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(
            v_wordRole_boxed_2134_,
            v_wordStart_boxed_2135_,
        );
    v_r_2137_ = crate::leanh::lean_box((v_res_2136_) as usize);
    return v_r_2137_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(
    mut v_patternChar_2138_: u32,
    mut v_wordChar_2139_: u32,
    mut v_patternRole_2140_: u8,
    mut v_wordRole_2141_: u8,
) -> u8 {
    let mut v___y_2143_: u32 = 0;
    let mut v___y_2144_: u32 = 0;
    let mut v___x_2145_: u8 = 0;
    let mut v___x_2146_: u8 = 0;
    let mut v___y_2148_: u32 = 0;
    let mut v___x_2149_: u32 = 0;
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2151_: u32 = 0;
    let mut v___x_2152_: u8 = 0;
    let mut v___x_2153_: u32 = 0;
    let mut v___x_2154_: u32 = 0;
    let mut v___x_2155_: u32 = 0;
    let mut v___x_2156_: u8 = 0;
    let mut v___x_2157_: u32 = 0;
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: u32 = 0;
    let mut v___x_2160_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2155_ = 65;
                v___x_2156_ = lean_uint32_dec_le(v___x_2155_, v_patternChar_2138_);
                if v___x_2156_ == 0 {
                    v___y_2148_ = v_patternChar_2138_;
                    state = 2;
                    continue;
                } else {
                    v___x_2157_ = 90;
                    v___x_2158_ = lean_uint32_dec_le(v_patternChar_2138_, v___x_2157_);
                    if v___x_2158_ == 0 {
                        v___y_2148_ = v_patternChar_2138_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2159_ = 32;
                        v___x_2160_ = lean_uint32_add(v_patternChar_2138_, v___x_2159_);
                        v___y_2148_ = v___x_2160_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2145_ = lean_uint32_dec_eq(v___y_2143_, v___y_2144_);
                if v___x_2145_ == 0 {
                    return v___x_2145_;
                } else {
                    if v_patternRole_2140_ == 0 {
                        if v_wordRole_2141_ == 0 {
                            return v___x_2145_;
                        } else {
                            v___x_2146_ = 0;
                            return v___x_2146_;
                        }
                    } else {
                        return v___x_2145_;
                    }
                }
            }
            2 => {
                v___x_2149_ = 65;
                v___x_2150_ = lean_uint32_dec_le(v___x_2149_, v_wordChar_2139_);
                if v___x_2150_ == 0 {
                    v___y_2143_ = v___y_2148_;
                    v___y_2144_ = v_wordChar_2139_;
                    state = 1;
                    continue;
                } else {
                    v___x_2151_ = 90;
                    v___x_2152_ = lean_uint32_dec_le(v_wordChar_2139_, v___x_2151_);
                    if v___x_2152_ == 0 {
                        v___y_2143_ = v___y_2148_;
                        v___y_2144_ = v_wordChar_2139_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2153_ = 32;
                        v___x_2154_ = lean_uint32_add(v_wordChar_2139_, v___x_2153_);
                        v___y_2143_ = v___y_2148_;
                        v___y_2144_ = v___x_2154_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch___boxed(
    mut v_patternChar_2161_: *mut crate::leanh::LeanObject,
    mut v_wordChar_2162_: *mut crate::leanh::LeanObject,
    mut v_patternRole_2163_: *mut crate::leanh::LeanObject,
    mut v_wordRole_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_patternChar_boxed_2165_: u32 = 0;
    let mut v_wordChar_boxed_2166_: u32 = 0;
    let mut v_patternRole_boxed_2167_: u8 = 0;
    let mut v_wordRole_boxed_2168_: u8 = 0;
    let mut v_res_2169_: u8 = 0;
    let mut v_r_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_patternChar_boxed_2165_ = crate::leanh::lean_unbox_uint32(v_patternChar_2161_);
    crate::leanh::lean_dec(v_patternChar_2161_);
    v_wordChar_boxed_2166_ = crate::leanh::lean_unbox_uint32(v_wordChar_2162_);
    crate::leanh::lean_dec(v_wordChar_2162_);
    v_patternRole_boxed_2167_ = (crate::leanh::lean_unbox(v_patternRole_2163_) as u8);
    v_wordRole_boxed_2168_ = (crate::leanh::lean_unbox(v_wordRole_2164_) as u8);
    v_res_2169_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(
            v_patternChar_boxed_2165_,
            v_wordChar_boxed_2166_,
            v_patternRole_boxed_2167_,
            v_wordRole_boxed_2168_,
        );
    v_r_2170_ = crate::leanh::lean_box((v_res_2169_) as usize);
    return v_r_2170_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0()
-> u16 {
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: u16 = 0;
    v___x_2171_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2172_ = lean_int16_of_nat(v___x_2171_);
    return v___x_2172_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1()
-> u16 {
    let mut v_score_2173_: u16 = 0;
    let mut v_score_2174_: u16 = 0;
    v_score_2173_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
    v_score_2174_ = lean_int16_add(v_score_2173_, v_score_2173_);
    return v_score_2174_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(
    mut v_pattern_2175_: *mut crate::leanh::LeanObject,
    mut v_word_2176_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2177_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2178_: *mut crate::leanh::LeanObject,
    mut v_patternRole_2179_: u8,
    mut v_wordRole_2180_: u8,
    mut v_consecutive_2181_: u16,
) -> u16 {
    let mut v_score_2183_: u16 = 0;
    let mut v___x_2184_: u16 = 0;
    let mut v___x_2185_: u8 = 0;
    let mut v_score_2186_: u16 = 0;
    let mut v_score_2188_: u16 = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: u16 = 0;
    let mut v_score_2192_: u16 = 0;
    let mut v___y_2194_: u16 = 0;
    let mut v___y_2195_: u8 = 0;
    let mut v___x_2196_: u16 = 0;
    let mut v_score_2197_: u16 = 0;
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_score_2200_: u16 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u8 = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v_score_2207_: u16 = 0;
    let mut v_score_2209_: u16 = 0;
    let mut v___y_2211_: u8 = 0;
    let mut v___x_2212_: u32 = 0;
    let mut v___x_2213_: u32 = 0;
    let mut v___x_2214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2198_ = crate::leanh::lean_unsigned_to_nat(1);
                v_score_2207_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
                v___x_2212_ = lean_string_utf8_get(v_pattern_2175_, v_patternIdx_2177_);
                v___x_2213_ = lean_string_utf8_get(v_word_2176_, v_wordIdx_2178_);
                v___x_2214_ = lean_uint32_dec_eq(v___x_2212_, v___x_2213_);
                if v___x_2214_ == 0 {
                    if v_patternRole_2179_ == 0 {
                        if v_wordRole_2180_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            v___y_2211_ = v___x_2214_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___y_2211_ = v___x_2214_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___y_2211_ = v___x_2214_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                v___x_2184_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
                v___x_2185_ = lean_int16_dec_le(v_consecutive_2181_, v___x_2184_);
                if v___x_2185_ == 0 {
                    v_score_2186_ = lean_int16_add(v_score_2183_, v_consecutive_2181_);
                    return v_score_2186_;
                } else {
                    return v_score_2183_;
                }
            }
            2 => {
                v___x_2189_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2190_ = lean_nat_dec_eq(v_wordIdx_2178_, v___x_2189_);
                if v___x_2190_ == 0 {
                    v_score_2183_ = v_score_2188_;
                    state = 1;
                    continue;
                } else {
                    v___x_2191_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__1);
                    v_score_2192_ = lean_int16_add(v_score_2188_, v___x_2191_);
                    v_score_2183_ = v_score_2192_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2195_ == 0 {
                    v_score_2188_ = v___y_2194_;
                    state = 2;
                    continue;
                } else {
                    v___x_2196_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__0);
                    v_score_2197_ = lean_int16_add(v___y_2194_, v___x_2196_);
                    v_score_2188_ = v_score_2197_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2201_ = lean_string_length(v_word_2176_);
                v___x_2202_ = lean_nat_sub(v___x_2201_, v___x_2198_);
                v___x_2203_ = lean_nat_dec_eq(v_wordIdx_2178_, v___x_2202_);
                crate::leanh::lean_dec(v___x_2202_);
                if v___x_2203_ == 0 {
                    v___y_2194_ = v_score_2200_;
                    v___y_2195_ = v___x_2203_;
                    state = 3;
                    continue;
                } else {
                    v___x_2204_ = lean_string_length(v_pattern_2175_);
                    v___x_2205_ = lean_nat_sub(v___x_2204_, v___x_2198_);
                    v___x_2206_ = lean_nat_dec_eq(v_patternIdx_2177_, v___x_2205_);
                    crate::leanh::lean_dec(v___x_2205_);
                    v___y_2194_ = v_score_2200_;
                    v___y_2195_ = v___x_2206_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v_score_2209_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___closed__1);
                v_score_2200_ = v_score_2209_;
                state = 4;
                continue;
            }
            6 => {
                if v___y_2211_ == 0 {
                    v_score_2200_ = v_score_2207_;
                    state = 4;
                    continue;
                } else {
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult___boxed(
    mut v_pattern_2215_: *mut crate::leanh::LeanObject,
    mut v_word_2216_: *mut crate::leanh::LeanObject,
    mut v_patternIdx_2217_: *mut crate::leanh::LeanObject,
    mut v_wordIdx_2218_: *mut crate::leanh::LeanObject,
    mut v_patternRole_2219_: *mut crate::leanh::LeanObject,
    mut v_wordRole_2220_: *mut crate::leanh::LeanObject,
    mut v_consecutive_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_patternRole_boxed_2222_: u8 = 0;
    let mut v_wordRole_boxed_2223_: u8 = 0;
    let mut v_consecutive_boxed_2224_: u16 = 0;
    let mut v_res_2225_: u16 = 0;
    let mut v_r_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_patternRole_boxed_2222_ = (crate::leanh::lean_unbox(v_patternRole_2219_) as u8);
    v_wordRole_boxed_2223_ = (crate::leanh::lean_unbox(v_wordRole_2220_) as u8);
    v_consecutive_boxed_2224_ = (crate::leanh::lean_unbox(v_consecutive_2221_) as u16);
    v_res_2225_ =
        l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(
            v_pattern_2215_,
            v_word_2216_,
            v_patternIdx_2217_,
            v_wordIdx_2218_,
            v_patternRole_boxed_2222_,
            v_wordRole_boxed_2223_,
            v_consecutive_boxed_2224_,
        );
    crate::leanh::lean_dec(v_wordIdx_2218_);
    crate::leanh::lean_dec(v_patternIdx_2217_);
    crate::leanh::lean_dec_ref(v_word_2216_);
    crate::leanh::lean_dec_ref(v_pattern_2215_);
    v_r_2226_ = crate::leanh::lean_box((v_res_2225_) as usize);
    return v_r_2226_;
}
pub unsafe fn l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(
    mut v_msg_2227_: *mut crate::leanh::LeanObject,
) -> u16 {
    let mut v___x_2228_: u16 = 0;
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: u16 = 0;
    v___x_2228_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
    v___x_2229_ = crate::leanh::lean_box((v___x_2228_) as usize);
    v___x_2230_ = lean_panic_fn_borrowed(v___x_2229_, v_msg_2227_);
    crate::leanh::lean_dec(v___x_2229_);
    v___x_2231_ = (crate::leanh::lean_unbox(v___x_2230_) as u16);
    crate::leanh::lean_dec(v___x_2230_);
    return v___x_2231_;
}
pub unsafe fn l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1___boxed(
    mut v_msg_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2233_: u16 = 0;
    let mut v_r_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2233_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v_msg_2232_);
    v_r_2234_ = crate::leanh::lean_box((v_res_2233_) as usize);
    return v_r_2234_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(
    mut v___x_2235_: *mut crate::leanh::LeanObject,
    mut v_a_2236_: *mut crate::leanh::LeanObject,
    mut v_x_2237_: u16,
) -> u16 {
    let mut v___x_2238_: u16 = 0;
    let mut v___x_2239_: u8 = 0;
    v___x_2238_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once
        ),
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1,
    );
    v___x_2239_ = lean_int16_dec_le(v_x_2237_, v___x_2238_);
    if v___x_2239_ == 0 {
        let mut v___x_2240_: u8 = 0;
        v___x_2240_ = lean_nat_dec_le(v___x_2235_, v_a_2236_);
        if v___x_2240_ == 0 {
            return v_x_2237_;
        } else {
            let mut v___x_2241_: u16 = 0;
            let mut v___x_2242_: u16 = 0;
            v___x_2241_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
            v___x_2242_ = lean_int16_add(v_x_2237_, v___x_2241_);
            return v___x_2242_;
        }
    } else {
        return v_x_2237_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2___boxed(
    mut v___x_2243_: *mut crate::leanh::LeanObject,
    mut v_a_2244_: *mut crate::leanh::LeanObject,
    mut v_x_2245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2246_: u16 = 0;
    let mut v_res_2247_: u16 = 0;
    let mut v_r_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2246_ = (crate::leanh::lean_unbox(v_x_2245_) as u16);
    v_res_2247_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_2243_, v_a_2244_, v_x_boxed_2246_);
    crate::leanh::lean_dec(v_a_2244_);
    crate::leanh::lean_dec(v___x_2243_);
    v_r_2248_ = crate::leanh::lean_box((v_res_2247_) as usize);
    return v_r_2248_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(
    mut v_pattern_2249_: *mut crate::leanh::LeanObject,
    mut v_word_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v___x_2253_: u8,
    mut v___x_2254_: u8,
    mut v___x_2255_: *mut crate::leanh::LeanObject,
    mut v_x_2256_: u16,
) -> u16 {
    let mut v_matchScore_2257_: u16 = 0;
    let mut v___x_2258_: u8 = 0;
    v_matchScore_2257_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once
        ),
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1,
    );
    v___x_2258_ = lean_int16_dec_le(v_x_2256_, v_matchScore_2257_);
    if v___x_2258_ == 0 {
        let mut v___x_2259_: u16 = 0;
        let mut v___x_2260_: u16 = 0;
        let mut v___x_2261_: u16 = 0;
        let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2264_: u16 = 0;
        let mut v___x_2265_: u16 = 0;
        v___x_2259_ = l_instInhabitedInt16;
        v___x_2260_ =
            l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(
                v_pattern_2249_,
                v_word_2250_,
                v_a_2251_,
                v_a_2252_,
                v___x_2253_,
                v___x_2254_,
                v_matchScore_2257_,
            );
        v___x_2261_ = lean_int16_add(v_x_2256_, v___x_2260_);
        v___x_2262_ = crate::leanh::lean_box((v___x_2259_) as usize);
        v___x_2263_ = lean_array_get(v___x_2262_, v___x_2255_, v_a_2252_);
        crate::leanh::lean_dec(v___x_2262_);
        v___x_2264_ = (crate::leanh::lean_unbox(v___x_2263_) as u16);
        crate::leanh::lean_dec(v___x_2263_);
        v___x_2265_ = lean_int16_sub(v___x_2261_, v___x_2264_);
        return v___x_2265_;
    } else {
        return v_x_2256_;
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3___boxed(
    mut v_pattern_2266_: *mut crate::leanh::LeanObject,
    mut v_word_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
    mut v_a_2269_: *mut crate::leanh::LeanObject,
    mut v___x_2270_: *mut crate::leanh::LeanObject,
    mut v___x_2271_: *mut crate::leanh::LeanObject,
    mut v___x_2272_: *mut crate::leanh::LeanObject,
    mut v_x_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3257__boxed_2274_: u8 = 0;
    let mut v___x_3258__boxed_2275_: u8 = 0;
    let mut v_x_boxed_2276_: u16 = 0;
    let mut v_res_2277_: u16 = 0;
    let mut v_r_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3257__boxed_2274_ = (crate::leanh::lean_unbox(v___x_2270_) as u8);
    v___x_3258__boxed_2275_ = (crate::leanh::lean_unbox(v___x_2271_) as u8);
    v_x_boxed_2276_ = (crate::leanh::lean_unbox(v_x_2273_) as u16);
    v_res_2277_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_2266_, v_word_2267_, v_a_2268_, v_a_2269_, v___x_3257__boxed_2274_, v___x_3258__boxed_2275_, v___x_2272_, v_x_boxed_2276_);
    crate::leanh::lean_dec_ref(v___x_2272_);
    crate::leanh::lean_dec(v_a_2269_);
    crate::leanh::lean_dec(v_a_2268_);
    crate::leanh::lean_dec_ref(v_word_2267_);
    crate::leanh::lean_dec_ref(v_pattern_2266_);
    v_r_2278_ = crate::leanh::lean_box((v_res_2277_) as usize);
    return v_r_2278_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(
    mut v_pattern_2279_: *mut crate::leanh::LeanObject,
    mut v_word_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_a_2282_: *mut crate::leanh::LeanObject,
    mut v___x_2283_: u8,
    mut v___x_2284_: u8,
    mut v___x_2285_: u16,
    mut v_x_2286_: u16,
) -> u16 {
    let mut v___y_2288_: u16 = 0;
    let mut v___x_2289_: u16 = 0;
    let mut v___x_2290_: u16 = 0;
    let mut v___x_2291_: u16 = 0;
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: u8 = 0;
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u16 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2291_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
                v___x_2292_ = lean_int16_dec_le(v_x_2286_, v___x_2291_);
                if v___x_2292_ == 0 {
                    v___x_2293_ = lean_int16_dec_eq(v___x_2285_, v___x_2291_);
                    if v___x_2293_ == 0 {
                        v___y_2288_ = v___x_2285_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2294_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
                        v___x_2295_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_2294_);
                        v___y_2288_ = v___x_2295_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_x_2286_;
                }
            }
            1 => {
                v___x_2289_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_2279_, v_word_2280_, v_a_2281_, v_a_2282_, v___x_2283_, v___x_2284_, v___y_2288_);
                v___x_2290_ = lean_int16_add(v_x_2286_, v___x_2289_);
                return v___x_2290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4___boxed(
    mut v_pattern_2296_: *mut crate::leanh::LeanObject,
    mut v_word_2297_: *mut crate::leanh::LeanObject,
    mut v_a_2298_: *mut crate::leanh::LeanObject,
    mut v_a_2299_: *mut crate::leanh::LeanObject,
    mut v___x_2300_: *mut crate::leanh::LeanObject,
    mut v___x_2301_: *mut crate::leanh::LeanObject,
    mut v___x_2302_: *mut crate::leanh::LeanObject,
    mut v_x_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3297__boxed_2304_: u8 = 0;
    let mut v___x_3298__boxed_2305_: u8 = 0;
    let mut v___x_3299__boxed_2306_: u16 = 0;
    let mut v_x_boxed_2307_: u16 = 0;
    let mut v_res_2308_: u16 = 0;
    let mut v_r_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3297__boxed_2304_ = (crate::leanh::lean_unbox(v___x_2300_) as u8);
    v___x_3298__boxed_2305_ = (crate::leanh::lean_unbox(v___x_2301_) as u8);
    v___x_3299__boxed_2306_ = (crate::leanh::lean_unbox(v___x_2302_) as u16);
    v_x_boxed_2307_ = (crate::leanh::lean_unbox(v_x_2303_) as u16);
    v_res_2308_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_2296_, v_word_2297_, v_a_2298_, v_a_2299_, v___x_3297__boxed_2304_, v___x_3298__boxed_2305_, v___x_3299__boxed_2306_, v_x_boxed_2307_);
    crate::leanh::lean_dec(v_a_2299_);
    crate::leanh::lean_dec(v_a_2298_);
    crate::leanh::lean_dec_ref(v_word_2297_);
    crate::leanh::lean_dec_ref(v_pattern_2296_);
    v_r_2309_ = crate::leanh::lean_box((v_res_2308_) as usize);
    return v_r_2309_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(
    mut v_word_2310_: *mut crate::leanh::LeanObject,
    mut v_a_2311_: *mut crate::leanh::LeanObject,
    mut v_pattern_2312_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2313_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2314_: *mut crate::leanh::LeanObject,
    mut v___x_2315_: *mut crate::leanh::LeanObject,
    mut v___x_2316_: *mut crate::leanh::LeanObject,
    mut v_range_2317_: *mut crate::leanh::LeanObject,
    mut v_b_2318_: *mut crate::leanh::LeanObject,
    mut v_i_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: u8 = 0;
    let mut v_fst_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v___x_2328_: u8 = 0;
    let mut v_matchScore_2329_: u16 = 0;
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2332_: u16 = 0;
    let mut v_runLengths_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchScore_2334_: u16 = 0;
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2353_: u16 = 0;
    let mut v___y_2354_: u16 = 0;
    let mut v___x_2355_: u16 = 0;
    let mut v___y_2357_: u16 = 0;
    let mut v___x_2358_: u32 = 0;
    let mut v___x_2359_: u32 = 0;
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: u8 = 0;
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u16 = 0;
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: u8 = 0;
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: u16 = 0;
    let mut v___x_2377_: u16 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: u16 = 0;
    let mut v___x_2381_: u16 = 0;
    let mut v___x_2382_: u8 = 0;
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: u16 = 0;
    let mut v___x_2385_: u16 = 0;
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: u16 = 0;
    let mut v___x_2394_: u16 = 0;
    let mut v___x_2395_: u16 = 0;
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u16 = 0;
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: u16 = 0;
    let mut v___x_2410_: u16 = 0;
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: u8 = 0;
    let mut v___x_2415_: u8 = 0;
    let mut v___x_2416_: u16 = 0;
    let mut v___x_2417_: u16 = 0;
    let mut v___x_2418_: u8 = 0;
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u16 = 0;
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: u16 = 0;
    let mut v___x_2434_: u16 = 0;
    let mut v___x_2435_: u8 = 0;
    let mut v___x_2436_: u16 = 0;
    let mut v___x_2437_: u16 = 0;
    let mut v_isSharedCheck_2438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2320_ = crate::leanh::lean_ctor_get(v_range_2317_, 1);
                v_step_2321_ = crate::leanh::lean_ctor_get(v_range_2317_, 2);
                v___x_2322_ = lean_nat_dec_lt(v_i_2319_, v_stop_2320_);
                if v___x_2322_ == 0 {
                    crate::leanh::lean_dec(v_i_2319_);
                    return v_b_2318_;
                } else {
                    v_fst_2323_ = crate::leanh::lean_ctor_get(v_b_2318_, 0);
                    v_snd_2324_ = crate::leanh::lean_ctor_get(v_b_2318_, 1);
                    v_isSharedCheck_2438_ = (!crate::leanh::lean_is_exclusive(v_b_2318_)) as u8;
                    if v_isSharedCheck_2438_ == 0 {
                        v___x_2326_ = v_b_2318_;
                        v_isShared_2327_ = v_isSharedCheck_2438_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2324_);
                        crate::leanh::lean_inc(v_fst_2323_);
                        crate::leanh::lean_dec(v_b_2318_);
                        v___x_2326_ = crate::leanh::lean_box(0);
                        v_isShared_2327_ = v_isSharedCheck_2438_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2328_ = 0;
                v_matchScore_2329_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
                v___x_2330_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2419_ = lean_nat_dec_le(v___x_2330_, v_i_2319_);
                if v___x_2419_ == 0 {
                    v___y_2357_ = v_matchScore_2329_;
                    state = 5;
                    continue;
                } else {
                    v___x_2420_ = lean_nat_sub(v_i_2319_, v___x_2330_);
                    v___x_2421_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
                    v___x_2422_ = lean_string_length(v_word_2310_);
                    v___x_2423_ = lean_nat_mul(v_a_2311_, v___x_2422_);
                    v___x_2424_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2425_ = lean_nat_mul(v___x_2423_, v___x_2424_);
                    crate::leanh::lean_dec(v___x_2423_);
                    v___x_2426_ = lean_nat_mul(v___x_2420_, v___x_2424_);
                    crate::leanh::lean_dec(v___x_2420_);
                    v___x_2427_ = lean_nat_add(v___x_2425_, v___x_2426_);
                    crate::leanh::lean_dec(v___x_2426_);
                    crate::leanh::lean_dec(v___x_2425_);
                    v___x_2428_ = crate::leanh::lean_box((v___x_2421_) as usize);
                    v___x_2429_ = lean_array_get(v___x_2428_, v_fst_2323_, v___x_2427_);
                    crate::leanh::lean_dec(v___x_2428_);
                    v___x_2430_ = lean_nat_add(v___x_2427_, v___x_2330_);
                    crate::leanh::lean_dec(v___x_2427_);
                    v___x_2431_ = crate::leanh::lean_box((v___x_2421_) as usize);
                    v___x_2432_ = lean_array_get(v___x_2431_, v_fst_2323_, v___x_2430_);
                    crate::leanh::lean_dec(v___x_2430_);
                    crate::leanh::lean_dec(v___x_2431_);
                    v___x_2433_ = (crate::leanh::lean_unbox(v___x_2429_) as u16);
                    v___x_2434_ = (crate::leanh::lean_unbox(v___x_2432_) as u16);
                    v___x_2435_ = lean_int16_dec_le(v___x_2433_, v___x_2434_);
                    if v___x_2435_ == 0 {
                        crate::leanh::lean_dec(v___x_2432_);
                        v___x_2436_ = (crate::leanh::lean_unbox(v___x_2429_) as u16);
                        crate::leanh::lean_dec(v___x_2429_);
                        v___y_2357_ = v___x_2436_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2429_);
                        v___x_2437_ = (crate::leanh::lean_unbox(v___x_2432_) as u16);
                        crate::leanh::lean_dec(v___x_2432_);
                        v___y_2357_ = v___x_2437_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2335_ = lean_string_length(v_word_2310_);
                v___x_2336_ = lean_nat_mul(v_a_2311_, v___x_2335_);
                v___x_2337_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2338_ = lean_nat_mul(v___x_2336_, v___x_2337_);
                crate::leanh::lean_dec(v___x_2336_);
                v___x_2339_ = lean_nat_mul(v_i_2319_, v___x_2337_);
                v_idx_2340_ = lean_nat_add(v___x_2338_, v___x_2339_);
                crate::leanh::lean_dec(v___x_2339_);
                crate::leanh::lean_dec(v___x_2338_);
                v___x_2341_ = crate::leanh::lean_box((v___y_2332_) as usize);
                v___x_2342_ = lean_array_set(v_fst_2323_, v_idx_2340_, v___x_2341_);
                v___x_2343_ = lean_nat_add(v_idx_2340_, v___x_2330_);
                crate::leanh::lean_dec(v_idx_2340_);
                v___x_2344_ = crate::leanh::lean_box((v_matchScore_2334_) as usize);
                v___x_2345_ = lean_array_set(v___x_2342_, v___x_2343_, v___x_2344_);
                crate::leanh::lean_dec(v___x_2343_);
                if v_isShared_2327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2326_, 1, v_runLengths_2333_);
                    crate::leanh::lean_ctor_set(v___x_2326_, 0, v___x_2345_);
                    v___x_2347_ = v___x_2326_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2350_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_runLengths_2333_);
                    v___x_2347_ = v_reuseFailAlloc_2350_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2348_ = lean_nat_add(v_i_2319_, v_step_2321_);
                crate::leanh::lean_dec(v_i_2319_);
                v_b_2318_ = v___x_2347_;
                v_i_2319_ = v___x_2348_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2355_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__2(v___x_2316_, v_i_2319_, v___y_2354_);
                v___y_2332_ = v___y_2353_;
                v_runLengths_2333_ = v___y_2352_;
                v_matchScore_2334_ = v___x_2355_;
                state = 2;
                continue;
            }
            5 => {
                v___x_2358_ = lean_string_utf8_get(v_pattern_2312_, v_a_2311_);
                v___x_2359_ = lean_string_utf8_get(v_word_2310_, v_i_2319_);
                v___x_2360_ = crate::leanh::lean_box((v___x_2328_) as usize);
                v___x_2361_ = lean_array_get(v___x_2360_, v_patternRoles_2313_, v_a_2311_);
                crate::leanh::lean_dec(v___x_2360_);
                v___x_2362_ = crate::leanh::lean_box((v___x_2328_) as usize);
                v___x_2363_ = lean_array_get(v___x_2362_, v_wordRoles_2314_, v_i_2319_);
                crate::leanh::lean_dec(v___x_2362_);
                v___x_2364_ = (crate::leanh::lean_unbox(v___x_2361_) as u8);
                v___x_2365_ = (crate::leanh::lean_unbox(v___x_2363_) as u8);
                v___x_2366_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_allowMatch(v___x_2358_, v___x_2359_, v___x_2364_, v___x_2365_);
                if v___x_2366_ == 0 {
                    crate::leanh::lean_dec(v___x_2363_);
                    crate::leanh::lean_dec(v___x_2361_);
                    v___y_2332_ = v___y_2357_;
                    v_runLengths_2333_ = v_snd_2324_;
                    v_matchScore_2334_ = v_matchScore_2329_;
                    state = 2;
                    continue;
                } else {
                    v___x_2367_ = lean_nat_dec_le(v___x_2330_, v_a_2311_);
                    if v___x_2367_ == 0 {
                        v___x_2368_ = lean_string_length(v_word_2310_);
                        v___x_2369_ = lean_nat_mul(v_a_2311_, v___x_2368_);
                        v___x_2370_ = lean_nat_add(v___x_2369_, v_i_2319_);
                        crate::leanh::lean_dec(v___x_2369_);
                        v___x_2371_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
                        v___x_2372_ = crate::leanh::lean_box((v___x_2371_) as usize);
                        v___x_2373_ = lean_array_set(v_snd_2324_, v___x_2370_, v___x_2372_);
                        crate::leanh::lean_dec(v___x_2370_);
                        v___x_2374_ = (crate::leanh::lean_unbox(v___x_2361_) as u8);
                        crate::leanh::lean_dec(v___x_2361_);
                        v___x_2375_ = (crate::leanh::lean_unbox(v___x_2363_) as u8);
                        crate::leanh::lean_dec(v___x_2363_);
                        v___x_2376_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_matchResult(v_pattern_2312_, v_word_2310_, v_a_2311_, v_i_2319_, v___x_2374_, v___x_2375_, v_matchScore_2329_);
                        v___x_2377_ = l_instInhabitedInt16;
                        v___x_2378_ = crate::leanh::lean_box((v___x_2377_) as usize);
                        v___x_2379_ = lean_array_get(v___x_2378_, v___x_2315_, v_i_2319_);
                        crate::leanh::lean_dec(v___x_2378_);
                        v___x_2380_ = (crate::leanh::lean_unbox(v___x_2379_) as u16);
                        crate::leanh::lean_dec(v___x_2379_);
                        v___x_2381_ = lean_int16_sub(v___x_2376_, v___x_2380_);
                        v___x_2382_ = lean_int16_dec_eq(v___x_2381_, v_matchScore_2329_);
                        if v___x_2382_ == 0 {
                            v___y_2332_ = v___y_2357_;
                            v_runLengths_2333_ = v___x_2373_;
                            v_matchScore_2334_ = v___x_2381_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2383_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_ofInt16_x21___closed__3);
                            v___x_2384_ = l_panic___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__1(v___x_2383_);
                            v___y_2332_ = v___y_2357_;
                            v_runLengths_2333_ = v___x_2373_;
                            v_matchScore_2334_ = v___x_2384_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2385_ = l_instInhabitedInt16;
                        v___x_2386_ = lean_nat_sub(v_a_2311_, v___x_2330_);
                        v___x_2387_ = lean_nat_sub(v_i_2319_, v___x_2330_);
                        v___x_2388_ = lean_string_length(v_word_2310_);
                        v___x_2389_ = lean_nat_mul(v___x_2386_, v___x_2388_);
                        crate::leanh::lean_dec(v___x_2386_);
                        v___x_2390_ = lean_nat_add(v___x_2389_, v___x_2387_);
                        v___x_2391_ = crate::leanh::lean_box((v___x_2385_) as usize);
                        v___x_2392_ = lean_array_get(v___x_2391_, v_snd_2324_, v___x_2390_);
                        crate::leanh::lean_dec(v___x_2390_);
                        crate::leanh::lean_dec(v___x_2391_);
                        v___x_2393_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
                        v___x_2394_ = (crate::leanh::lean_unbox(v___x_2392_) as u16);
                        crate::leanh::lean_dec(v___x_2392_);
                        v___x_2395_ = lean_int16_add(v___x_2394_, v___x_2393_);
                        v___x_2396_ = lean_nat_mul(v_a_2311_, v___x_2388_);
                        v___x_2397_ = lean_nat_add(v___x_2396_, v_i_2319_);
                        crate::leanh::lean_dec(v___x_2396_);
                        v___x_2398_ = crate::leanh::lean_box((v___x_2395_) as usize);
                        v___x_2399_ = lean_array_set(v_snd_2324_, v___x_2397_, v___x_2398_);
                        crate::leanh::lean_dec(v___x_2397_);
                        v___x_2400_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
                        v___x_2401_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2402_ = lean_nat_mul(v___x_2389_, v___x_2401_);
                        crate::leanh::lean_dec(v___x_2389_);
                        v___x_2403_ = lean_nat_mul(v___x_2387_, v___x_2401_);
                        crate::leanh::lean_dec(v___x_2387_);
                        v___x_2404_ = lean_nat_add(v___x_2402_, v___x_2403_);
                        crate::leanh::lean_dec(v___x_2403_);
                        crate::leanh::lean_dec(v___x_2402_);
                        v___x_2405_ = crate::leanh::lean_box((v___x_2400_) as usize);
                        v___x_2406_ = lean_array_get(v___x_2405_, v_fst_2323_, v___x_2404_);
                        crate::leanh::lean_dec(v___x_2405_);
                        v___x_2407_ = (crate::leanh::lean_unbox(v___x_2361_) as u8);
                        v___x_2408_ = (crate::leanh::lean_unbox(v___x_2363_) as u8);
                        v___x_2409_ = (crate::leanh::lean_unbox(v___x_2406_) as u16);
                        crate::leanh::lean_dec(v___x_2406_);
                        v___x_2410_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__3(v_pattern_2312_, v_word_2310_, v_a_2311_, v_i_2319_, v___x_2407_, v___x_2408_, v___x_2315_, v___x_2409_);
                        v___x_2411_ = lean_nat_add(v___x_2404_, v___x_2330_);
                        crate::leanh::lean_dec(v___x_2404_);
                        v___x_2412_ = crate::leanh::lean_box((v___x_2400_) as usize);
                        v___x_2413_ = lean_array_get(v___x_2412_, v_fst_2323_, v___x_2411_);
                        crate::leanh::lean_dec(v___x_2411_);
                        crate::leanh::lean_dec(v___x_2412_);
                        v___x_2414_ = (crate::leanh::lean_unbox(v___x_2361_) as u8);
                        crate::leanh::lean_dec(v___x_2361_);
                        v___x_2415_ = (crate::leanh::lean_unbox(v___x_2363_) as u8);
                        crate::leanh::lean_dec(v___x_2363_);
                        v___x_2416_ = (crate::leanh::lean_unbox(v___x_2413_) as u16);
                        crate::leanh::lean_dec(v___x_2413_);
                        v___x_2417_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_map___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__4(v_pattern_2312_, v_word_2310_, v_a_2311_, v_i_2319_, v___x_2414_, v___x_2415_, v___x_2395_, v___x_2416_);
                        v___x_2418_ = lean_int16_dec_le(v___x_2410_, v___x_2417_);
                        if v___x_2418_ == 0 {
                            v___y_2352_ = v___x_2399_;
                            v___y_2353_ = v___y_2357_;
                            v___y_2354_ = v___x_2410_;
                            state = 4;
                            continue;
                        } else {
                            v___y_2352_ = v___x_2399_;
                            v___y_2353_ = v___y_2357_;
                            v___y_2354_ = v___x_2417_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg___boxed(
    mut v_word_2439_: *mut crate::leanh::LeanObject,
    mut v_a_2440_: *mut crate::leanh::LeanObject,
    mut v_pattern_2441_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2442_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2443_: *mut crate::leanh::LeanObject,
    mut v___x_2444_: *mut crate::leanh::LeanObject,
    mut v___x_2445_: *mut crate::leanh::LeanObject,
    mut v_range_2446_: *mut crate::leanh::LeanObject,
    mut v_b_2447_: *mut crate::leanh::LeanObject,
    mut v_i_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2449_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_2439_, v_a_2440_, v_pattern_2441_, v_patternRoles_2442_, v_wordRoles_2443_, v___x_2444_, v___x_2445_, v_range_2446_, v_b_2447_, v_i_2448_);
    crate::leanh::lean_dec_ref(v_range_2446_);
    crate::leanh::lean_dec(v___x_2445_);
    crate::leanh::lean_dec_ref(v___x_2444_);
    crate::leanh::lean_dec_ref(v_wordRoles_2443_);
    crate::leanh::lean_dec_ref(v_patternRoles_2442_);
    crate::leanh::lean_dec_ref(v_pattern_2441_);
    crate::leanh::lean_dec(v_a_2440_);
    crate::leanh::lean_dec_ref(v_word_2439_);
    return v_res_2449_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(
    mut v___x_2450_: *mut crate::leanh::LeanObject,
    mut v___x_2451_: *mut crate::leanh::LeanObject,
    mut v_word_2452_: *mut crate::leanh::LeanObject,
    mut v_pattern_2453_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2454_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2455_: *mut crate::leanh::LeanObject,
    mut v___x_2456_: *mut crate::leanh::LeanObject,
    mut v___x_2457_: *mut crate::leanh::LeanObject,
    mut v_range_2458_: *mut crate::leanh::LeanObject,
    mut v_b_2459_: *mut crate::leanh::LeanObject,
    mut v_i_2460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut v_fst_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2481_: u8 = 0;
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_reuseFailAlloc_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2461_ = crate::leanh::lean_ctor_get(v_range_2458_, 1);
                v_step_2462_ = crate::leanh::lean_ctor_get(v_range_2458_, 2);
                v___x_2463_ = lean_nat_dec_lt(v_i_2460_, v_stop_2461_);
                if v___x_2463_ == 0 {
                    crate::leanh::lean_dec(v_i_2460_);
                    return v_b_2459_;
                } else {
                    v_fst_2464_ = crate::leanh::lean_ctor_get(v_b_2459_, 0);
                    v_snd_2465_ = crate::leanh::lean_ctor_get(v_b_2459_, 1);
                    v_isSharedCheck_2489_ = (!crate::leanh::lean_is_exclusive(v_b_2459_)) as u8;
                    if v_isSharedCheck_2489_ == 0 {
                        v___x_2467_ = v_b_2459_;
                        v_isShared_2468_ = v_isSharedCheck_2489_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2465_);
                        crate::leanh::lean_inc(v_fst_2464_);
                        crate::leanh::lean_dec(v_b_2459_);
                        v___x_2467_ = crate::leanh::lean_box(0);
                        v_isShared_2468_ = v_isSharedCheck_2489_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2469_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2470_ = lean_nat_sub(v___x_2450_, v_i_2460_);
                v___x_2471_ = lean_nat_sub(v___x_2470_, v___x_2469_);
                crate::leanh::lean_dec(v___x_2470_);
                v___x_2472_ = lean_nat_sub(v___x_2451_, v___x_2471_);
                crate::leanh::lean_dec(v___x_2471_);
                crate::leanh::lean_inc(v_i_2460_);
                v___x_2473_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2473_, 0, v_i_2460_);
                crate::leanh::lean_ctor_set(v___x_2473_, 1, v___x_2472_);
                crate::leanh::lean_ctor_set(v___x_2473_, 2, v___x_2469_);
                if v_isShared_2468_ == 0 {
                    v___x_2475_ = v___x_2467_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_fst_2464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_snd_2465_);
                    v___x_2475_ = v_reuseFailAlloc_2488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_i_2460_);
                v___x_2476_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_2452_, v_i_2460_, v_pattern_2453_, v_patternRoles_2454_, v_wordRoles_2455_, v___x_2456_, v___x_2457_, v___x_2473_, v___x_2475_, v_i_2460_);
                crate::leanh::lean_dec_ref_known(v___x_2473_, 3);
                v_fst_2477_ = crate::leanh::lean_ctor_get(v___x_2476_, 0);
                v_snd_2478_ = crate::leanh::lean_ctor_get(v___x_2476_, 1);
                v_isSharedCheck_2487_ = (!crate::leanh::lean_is_exclusive(v___x_2476_)) as u8;
                if v_isSharedCheck_2487_ == 0 {
                    v___x_2480_ = v___x_2476_;
                    v_isShared_2481_ = v_isSharedCheck_2487_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2478_);
                    crate::leanh::lean_inc(v_fst_2477_);
                    crate::leanh::lean_dec(v___x_2476_);
                    v___x_2480_ = crate::leanh::lean_box(0);
                    v_isShared_2481_ = v_isSharedCheck_2487_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2481_ == 0 {
                    v___x_2483_ = v___x_2480_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2486_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_fst_2477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_snd_2478_);
                    v___x_2483_ = v_reuseFailAlloc_2486_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2484_ = lean_nat_add(v_i_2460_, v_step_2462_);
                crate::leanh::lean_dec(v_i_2460_);
                v_b_2459_ = v___x_2483_;
                v_i_2460_ = v___x_2484_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg___boxed(
    mut v___x_2490_: *mut crate::leanh::LeanObject,
    mut v___x_2491_: *mut crate::leanh::LeanObject,
    mut v_word_2492_: *mut crate::leanh::LeanObject,
    mut v_pattern_2493_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2494_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2495_: *mut crate::leanh::LeanObject,
    mut v___x_2496_: *mut crate::leanh::LeanObject,
    mut v___x_2497_: *mut crate::leanh::LeanObject,
    mut v_range_2498_: *mut crate::leanh::LeanObject,
    mut v_b_2499_: *mut crate::leanh::LeanObject,
    mut v_i_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2501_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_2490_, v___x_2491_, v_word_2492_, v_pattern_2493_, v_patternRoles_2494_, v_wordRoles_2495_, v___x_2496_, v___x_2497_, v_range_2498_, v_b_2499_, v_i_2500_);
    crate::leanh::lean_dec_ref(v_range_2498_);
    crate::leanh::lean_dec(v___x_2497_);
    crate::leanh::lean_dec_ref(v___x_2496_);
    crate::leanh::lean_dec_ref(v_wordRoles_2495_);
    crate::leanh::lean_dec_ref(v_patternRoles_2494_);
    crate::leanh::lean_dec_ref(v_pattern_2493_);
    crate::leanh::lean_dec_ref(v_word_2492_);
    crate::leanh::lean_dec(v___x_2491_);
    crate::leanh::lean_dec(v___x_2490_);
    return v_res_2501_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(
    mut v_word_2502_: *mut crate::leanh::LeanObject,
    mut v_pattern_2503_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2504_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2505_: *mut crate::leanh::LeanObject,
    mut v___x_2506_: *mut crate::leanh::LeanObject,
    mut v___x_2507_: *mut crate::leanh::LeanObject,
    mut v___x_2508_: *mut crate::leanh::LeanObject,
    mut v___x_2509_: *mut crate::leanh::LeanObject,
    mut v_range_2510_: *mut crate::leanh::LeanObject,
    mut v_b_2511_: *mut crate::leanh::LeanObject,
    mut v_i_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: u8 = 0;
    let mut v_fst_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2520_: u8 = 0;
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2533_: u8 = 0;
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut v_reuseFailAlloc_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2513_ = crate::leanh::lean_ctor_get(v_range_2510_, 1);
                v_step_2514_ = crate::leanh::lean_ctor_get(v_range_2510_, 2);
                v___x_2515_ = lean_nat_dec_lt(v_i_2512_, v_stop_2513_);
                if v___x_2515_ == 0 {
                    crate::leanh::lean_dec(v_i_2512_);
                    return v_b_2511_;
                } else {
                    v_fst_2516_ = crate::leanh::lean_ctor_get(v_b_2511_, 0);
                    v_snd_2517_ = crate::leanh::lean_ctor_get(v_b_2511_, 1);
                    v_isSharedCheck_2541_ = (!crate::leanh::lean_is_exclusive(v_b_2511_)) as u8;
                    if v_isSharedCheck_2541_ == 0 {
                        v___x_2519_ = v_b_2511_;
                        v_isShared_2520_ = v_isSharedCheck_2541_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2517_);
                        crate::leanh::lean_inc(v_fst_2516_);
                        crate::leanh::lean_dec(v_b_2511_);
                        v___x_2519_ = crate::leanh::lean_box(0);
                        v_isShared_2520_ = v_isSharedCheck_2541_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2521_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2522_ = lean_nat_sub(v___x_2508_, v_i_2512_);
                v___x_2523_ = lean_nat_sub(v___x_2522_, v___x_2521_);
                crate::leanh::lean_dec(v___x_2522_);
                v___x_2524_ = lean_nat_sub(v___x_2509_, v___x_2523_);
                crate::leanh::lean_dec(v___x_2523_);
                crate::leanh::lean_inc(v_i_2512_);
                v___x_2525_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2525_, 0, v_i_2512_);
                crate::leanh::lean_ctor_set(v___x_2525_, 1, v___x_2524_);
                crate::leanh::lean_ctor_set(v___x_2525_, 2, v___x_2521_);
                if v_isShared_2520_ == 0 {
                    v___x_2527_ = v___x_2519_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_fst_2516_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_snd_2517_);
                    v___x_2527_ = v_reuseFailAlloc_2540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_i_2512_);
                v___x_2528_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_2502_, v_i_2512_, v_pattern_2503_, v_patternRoles_2504_, v_wordRoles_2505_, v___x_2506_, v___x_2507_, v___x_2525_, v___x_2527_, v_i_2512_);
                crate::leanh::lean_dec_ref_known(v___x_2525_, 3);
                v_fst_2529_ = crate::leanh::lean_ctor_get(v___x_2528_, 0);
                v_snd_2530_ = crate::leanh::lean_ctor_get(v___x_2528_, 1);
                v_isSharedCheck_2539_ = (!crate::leanh::lean_is_exclusive(v___x_2528_)) as u8;
                if v_isSharedCheck_2539_ == 0 {
                    v___x_2532_ = v___x_2528_;
                    v_isShared_2533_ = v_isSharedCheck_2539_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2530_);
                    crate::leanh::lean_inc(v_fst_2529_);
                    crate::leanh::lean_dec(v___x_2528_);
                    v___x_2532_ = crate::leanh::lean_box(0);
                    v_isShared_2533_ = v_isSharedCheck_2539_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2533_ == 0 {
                    v___x_2535_ = v___x_2532_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_fst_2529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_snd_2530_);
                    v___x_2535_ = v_reuseFailAlloc_2538_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2536_ = lean_nat_add(v_i_2512_, v_step_2514_);
                crate::leanh::lean_dec(v_i_2512_);
                v___x_2537_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_2508_, v___x_2509_, v_word_2502_, v_pattern_2503_, v_patternRoles_2504_, v_wordRoles_2505_, v___x_2506_, v___x_2507_, v_range_2510_, v___x_2535_, v___x_2536_);
                return v___x_2537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg___boxed(
    mut v_word_2542_: *mut crate::leanh::LeanObject,
    mut v_pattern_2543_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2544_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2545_: *mut crate::leanh::LeanObject,
    mut v___x_2546_: *mut crate::leanh::LeanObject,
    mut v___x_2547_: *mut crate::leanh::LeanObject,
    mut v___x_2548_: *mut crate::leanh::LeanObject,
    mut v___x_2549_: *mut crate::leanh::LeanObject,
    mut v_range_2550_: *mut crate::leanh::LeanObject,
    mut v_b_2551_: *mut crate::leanh::LeanObject,
    mut v_i_2552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2553_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_2542_, v_pattern_2543_, v_patternRoles_2544_, v_wordRoles_2545_, v___x_2546_, v___x_2547_, v___x_2548_, v___x_2549_, v_range_2550_, v_b_2551_, v_i_2552_);
    crate::leanh::lean_dec_ref(v_range_2550_);
    crate::leanh::lean_dec(v___x_2549_);
    crate::leanh::lean_dec(v___x_2548_);
    crate::leanh::lean_dec(v___x_2547_);
    crate::leanh::lean_dec_ref(v___x_2546_);
    crate::leanh::lean_dec_ref(v_wordRoles_2545_);
    crate::leanh::lean_dec_ref(v_patternRoles_2544_);
    crate::leanh::lean_dec_ref(v_pattern_2543_);
    crate::leanh::lean_dec_ref(v_word_2542_);
    return v_res_2553_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(
    mut v_wordRoles_2554_: *mut crate::leanh::LeanObject,
    mut v_range_2555_: *mut crate::leanh::LeanObject,
    mut v_b_2556_: *mut crate::leanh::LeanObject,
    mut v_i_2557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: u8 = 0;
    let mut v_snd_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v_fst_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2570_: u8 = 0;
    let mut v_fst_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v___x_2576_: u8 = 0;
    let mut v_lastSepIdx_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastSepIdx_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_penaltyNs_2580_: u16 = 0;
    let mut v_penaltySkip_2581_: u16 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: u8 = 0;
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: u16 = 0;
    let mut v___x_2587_: u16 = 0;
    let mut v___x_2588_: u16 = 0;
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v_penaltyNs_2608_: u16 = 0;
    let mut v___x_2609_: u16 = 0;
    let mut v___x_2610_: u16 = 0;
    let mut v___x_2611_: u16 = 0;
    let mut v___x_2612_: u16 = 0;
    let mut v___x_2613_: u16 = 0;
    let mut v___x_2614_: u16 = 0;
    let mut v___x_2615_: u16 = 0;
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut v_unused_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2619_: u8 = 0;
    let mut v_unused_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2558_ = crate::leanh::lean_ctor_get(v_range_2555_, 1);
                v_step_2559_ = crate::leanh::lean_ctor_get(v_range_2555_, 2);
                v___x_2560_ = lean_nat_dec_lt(v_i_2557_, v_stop_2558_);
                if v___x_2560_ == 0 {
                    crate::leanh::lean_dec(v_i_2557_);
                    return v_b_2556_;
                } else {
                    v_snd_2561_ = crate::leanh::lean_ctor_get(v_b_2556_, 1);
                    crate::leanh::lean_inc(v_snd_2561_);
                    v_snd_2562_ = crate::leanh::lean_ctor_get(v_snd_2561_, 1);
                    crate::leanh::lean_inc(v_snd_2562_);
                    v_fst_2563_ = crate::leanh::lean_ctor_get(v_b_2556_, 0);
                    v_isSharedCheck_2619_ = (!crate::leanh::lean_is_exclusive(v_b_2556_)) as u8;
                    if v_isSharedCheck_2619_ == 0 {
                        v_unused_2620_ = crate::leanh::lean_ctor_get(v_b_2556_, 1);
                        crate::leanh::lean_dec(v_unused_2620_);
                        v___x_2565_ = v_b_2556_;
                        v_isShared_2566_ = v_isSharedCheck_2619_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2563_);
                        crate::leanh::lean_dec(v_b_2556_);
                        v___x_2565_ = crate::leanh::lean_box(0);
                        v_isShared_2566_ = v_isSharedCheck_2619_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2567_ = crate::leanh::lean_ctor_get(v_snd_2561_, 0);
                v_isSharedCheck_2617_ = (!crate::leanh::lean_is_exclusive(v_snd_2561_)) as u8;
                if v_isSharedCheck_2617_ == 0 {
                    v_unused_2618_ = crate::leanh::lean_ctor_get(v_snd_2561_, 1);
                    crate::leanh::lean_dec(v_unused_2618_);
                    v___x_2569_ = v_snd_2561_;
                    v_isShared_2570_ = v_isSharedCheck_2617_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2567_);
                    crate::leanh::lean_dec(v_snd_2561_);
                    v___x_2569_ = crate::leanh::lean_box(0);
                    v_isShared_2570_ = v_isSharedCheck_2617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_2571_ = crate::leanh::lean_ctor_get(v_snd_2562_, 0);
                v_snd_2572_ = crate::leanh::lean_ctor_get(v_snd_2562_, 1);
                v_isSharedCheck_2616_ = (!crate::leanh::lean_is_exclusive(v_snd_2562_)) as u8;
                if v_isSharedCheck_2616_ == 0 {
                    v___x_2574_ = v_snd_2562_;
                    v_isShared_2575_ = v_isSharedCheck_2616_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2572_);
                    crate::leanh::lean_inc(v_fst_2571_);
                    crate::leanh::lean_dec(v_snd_2562_);
                    v___x_2574_ = crate::leanh::lean_box(0);
                    v_isShared_2575_ = v_isSharedCheck_2616_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2576_ = 0;
                v_lastSepIdx_2577_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2604_ = lean_nat_dec_eq(v_i_2557_, v_lastSepIdx_2577_);
                if v___x_2604_ == 0 {
                    v___x_2605_ = crate::leanh::lean_box((v___x_2576_) as usize);
                    v___x_2606_ = lean_array_get(v___x_2605_, v_wordRoles_2554_, v_i_2557_);
                    crate::leanh::lean_dec(v___x_2605_);
                    v___x_2607_ = (crate::leanh::lean_unbox(v___x_2606_) as u8);
                    crate::leanh::lean_dec(v___x_2606_);
                    if v___x_2607_ == 2 {
                        crate::leanh::lean_dec(v_snd_2572_);
                        crate::leanh::lean_dec(v_fst_2567_);
                        v_penaltyNs_2608_ = crate::leanh::lean_uint16_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once
                            ),
                            _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0,
                        );
                        v___x_2609_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty___closed__0);
                        v___x_2610_ = (crate::leanh::lean_unbox(v_fst_2571_) as u16);
                        crate::leanh::lean_dec(v_fst_2571_);
                        v___x_2611_ = lean_int16_add(v___x_2610_, v___x_2609_);
                        crate::leanh::lean_inc(v_i_2557_);
                        v_lastSepIdx_2579_ = v_i_2557_;
                        v_penaltyNs_2580_ = v___x_2611_;
                        v_penaltySkip_2581_ = v_penaltyNs_2608_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2612_ = (crate::leanh::lean_unbox(v_fst_2571_) as u16);
                        crate::leanh::lean_dec(v_fst_2571_);
                        v___x_2613_ = (crate::leanh::lean_unbox(v_snd_2572_) as u16);
                        crate::leanh::lean_dec(v_snd_2572_);
                        v_lastSepIdx_2579_ = v_fst_2567_;
                        v_penaltyNs_2580_ = v___x_2612_;
                        v_penaltySkip_2581_ = v___x_2613_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2614_ = (crate::leanh::lean_unbox(v_fst_2571_) as u16);
                    crate::leanh::lean_dec(v_fst_2571_);
                    v___x_2615_ = (crate::leanh::lean_unbox(v_snd_2572_) as u16);
                    crate::leanh::lean_dec(v_snd_2572_);
                    v_lastSepIdx_2579_ = v_fst_2567_;
                    v_penaltyNs_2580_ = v___x_2614_;
                    v_penaltySkip_2581_ = v___x_2615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2582_ = crate::leanh::lean_box((v___x_2576_) as usize);
                v___x_2583_ = lean_array_get(v___x_2582_, v_wordRoles_2554_, v_i_2557_);
                crate::leanh::lean_dec(v___x_2582_);
                v___x_2584_ = lean_nat_dec_eq(v_i_2557_, v_lastSepIdx_2577_);
                v___x_2585_ = (crate::leanh::lean_unbox(v___x_2583_) as u8);
                crate::leanh::lean_dec(v___x_2583_);
                v___x_2586_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_skipPenalty(v___x_2585_, v___x_2584_);
                v___x_2587_ = lean_int16_add(v_penaltySkip_2581_, v___x_2586_);
                v___x_2588_ = lean_int16_add(v___x_2587_, v_penaltyNs_2580_);
                v___x_2589_ = crate::leanh::lean_box((v___x_2588_) as usize);
                v___x_2590_ = lean_array_set(v_fst_2563_, v_i_2557_, v___x_2589_);
                v___x_2591_ = crate::leanh::lean_box((v_penaltyNs_2580_) as usize);
                v___x_2592_ = crate::leanh::lean_box((v___x_2587_) as usize);
                if v_isShared_2575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2574_, 1, v___x_2592_);
                    crate::leanh::lean_ctor_set(v___x_2574_, 0, v___x_2591_);
                    v___x_2594_ = v___x_2574_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2592_);
                    v___x_2594_ = v_reuseFailAlloc_2603_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2570_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2569_, 1, v___x_2594_);
                    crate::leanh::lean_ctor_set(v___x_2569_, 0, v_lastSepIdx_2579_);
                    v___x_2596_ = v___x_2569_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2602_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_lastSepIdx_2579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 1, v___x_2594_);
                    v___x_2596_ = v_reuseFailAlloc_2602_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2566_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2565_, 1, v___x_2596_);
                    crate::leanh::lean_ctor_set(v___x_2565_, 0, v___x_2590_);
                    v___x_2598_ = v___x_2565_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2590_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 1, v___x_2596_);
                    v___x_2598_ = v_reuseFailAlloc_2601_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2599_ = lean_nat_add(v_i_2557_, v_step_2559_);
                crate::leanh::lean_dec(v_i_2557_);
                v_b_2556_ = v___x_2598_;
                v_i_2557_ = v___x_2599_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg___boxed(
    mut v_wordRoles_2621_: *mut crate::leanh::LeanObject,
    mut v_range_2622_: *mut crate::leanh::LeanObject,
    mut v_b_2623_: *mut crate::leanh::LeanObject,
    mut v_i_2624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2625_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_2621_, v_range_2622_, v_b_2623_, v_i_2624_);
    crate::leanh::lean_dec_ref(v_range_2622_);
    crate::leanh::lean_dec_ref(v_wordRoles_2621_);
    return v_res_2625_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_penaltyNs_2626_: u16 = 0;
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_penaltyNs_2626_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once),
        _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0,
    );
    v___x_2627_ = crate::leanh::lean_box((v_penaltyNs_2626_) as usize);
    v___x_2628_ = crate::leanh::lean_box((v_penaltyNs_2626_) as usize);
    v___x_2629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2629_, 0, v___x_2627_);
    crate::leanh::lean_ctor_set(v___x_2629_, 1, v___x_2628_);
    return v___x_2629_;
}
pub unsafe fn _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastSepIdx_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2630_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__0);
    v_lastSepIdx_2631_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2632_, 0, v_lastSepIdx_2631_);
    crate::leanh::lean_ctor_set(v___x_2632_, 1, v___x_2630_);
    return v___x_2632_;
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(
    mut v_pattern_2633_: *mut crate::leanh::LeanObject,
    mut v_word_2634_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2635_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2638_: u16 = 0;
    let mut v___x_2639_: u16 = 0;
    let mut v___x_2640_: u8 = 0;
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastSepIdx_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_penaltyNs_2650_: u16 = 0;
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_runLengths_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPenalties_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2665_: u8 = 0;
    let mut v_matchScore_2666_: u16 = 0;
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: u16 = 0;
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: u16 = 0;
    let mut v___x_2687_: u16 = 0;
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: u16 = 0;
    let mut v___x_2690_: u16 = 0;
    let mut v_reuseFailAlloc_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_unused_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2644_ = lean_string_length(v_pattern_2633_);
                v___x_2645_ = lean_string_length(v_word_2634_);
                v___x_2646_ = lean_nat_mul(v___x_2644_, v___x_2645_);
                v___x_2647_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2648_ = lean_nat_mul(v___x_2646_, v___x_2647_);
                v_lastSepIdx_2649_ = crate::leanh::lean_unsigned_to_nat(0);
                v_penaltyNs_2650_ = crate::leanh::lean_uint16_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0_once
                    ),
                    _init_l_Lean_FuzzyMatching_instInhabitedScore_default___closed__0,
                );
                v___x_2651_ = crate::leanh::lean_box((v_penaltyNs_2650_) as usize);
                v_runLengths_2652_ = lean_mk_array(v___x_2646_, v___x_2651_);
                v___x_2653_ = crate::leanh::lean_box((v_penaltyNs_2650_) as usize);
                v_startPenalties_2654_ = lean_mk_array(v___x_2645_, v___x_2653_);
                v___x_2655_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2656_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2656_, 0, v_lastSepIdx_2649_);
                crate::leanh::lean_ctor_set(v___x_2656_, 1, v___x_2645_);
                crate::leanh::lean_ctor_set(v___x_2656_, 2, v___x_2655_);
                v___x_2657_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___closed__1);
                v___x_2658_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2658_, 0, v_startPenalties_2654_);
                crate::leanh::lean_ctor_set(v___x_2658_, 1, v___x_2657_);
                v___x_2659_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_2636_, v___x_2656_, v___x_2658_, v_lastSepIdx_2649_);
                crate::leanh::lean_dec_ref_known(v___x_2656_, 3);
                v_snd_2660_ = crate::leanh::lean_ctor_get(v___x_2659_, 1);
                crate::leanh::lean_inc(v_snd_2660_);
                v_fst_2661_ = crate::leanh::lean_ctor_get(v___x_2659_, 0);
                crate::leanh::lean_inc(v_fst_2661_);
                crate::leanh::lean_dec_ref(v___x_2659_);
                v_fst_2662_ = crate::leanh::lean_ctor_get(v_snd_2660_, 0);
                v_isSharedCheck_2692_ = (!crate::leanh::lean_is_exclusive(v_snd_2660_)) as u8;
                if v_isSharedCheck_2692_ == 0 {
                    v_unused_2693_ = crate::leanh::lean_ctor_get(v_snd_2660_, 1);
                    crate::leanh::lean_dec(v_unused_2693_);
                    v___x_2664_ = v_snd_2660_;
                    v_isShared_2665_ = v_isSharedCheck_2692_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2662_);
                    crate::leanh::lean_dec(v_snd_2660_);
                    v___x_2664_ = crate::leanh::lean_box(0);
                    v_isShared_2665_ = v_isSharedCheck_2692_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2639_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
                v___x_2640_ = lean_int16_dec_le(v___y_2638_, v___x_2639_);
                if v___x_2640_ == 0 {
                    v___x_2641_ = lean_int16_to_int(v___y_2638_);
                    v___x_2642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2641_);
                    return v___x_2642_;
                } else {
                    v___x_2643_ = crate::leanh::lean_box(0);
                    return v___x_2643_;
                }
            }
            2 => {
                v_matchScore_2666_ = crate::leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1_once), _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful___closed__1);
                v___x_2667_ = crate::leanh::lean_box((v_matchScore_2666_) as usize);
                v_result_2668_ = lean_mk_array(v___x_2648_, v___x_2667_);
                v___x_2669_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2669_, 0, v_lastSepIdx_2649_);
                crate::leanh::lean_ctor_set(v___x_2669_, 1, v___x_2644_);
                crate::leanh::lean_ctor_set(v___x_2669_, 2, v___x_2655_);
                if v_isShared_2665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2664_, 1, v_runLengths_2652_);
                    crate::leanh::lean_ctor_set(v___x_2664_, 0, v_result_2668_);
                    v___x_2671_ = v___x_2664_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_result_2668_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_runLengths_2652_);
                    v___x_2671_ = v_reuseFailAlloc_2691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2672_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_2634_, v_pattern_2633_, v_patternRoles_2635_, v_wordRoles_2636_, v_fst_2661_, v_fst_2662_, v___x_2644_, v___x_2645_, v___x_2669_, v___x_2671_, v_lastSepIdx_2649_);
                crate::leanh::lean_dec_ref_known(v___x_2669_, 3);
                crate::leanh::lean_dec(v_fst_2662_);
                crate::leanh::lean_dec(v_fst_2661_);
                v_fst_2673_ = crate::leanh::lean_ctor_get(v___x_2672_, 0);
                crate::leanh::lean_inc(v_fst_2673_);
                crate::leanh::lean_dec_ref(v___x_2672_);
                v___x_2674_ = lean_nat_sub(v___x_2644_, v___x_2655_);
                v___x_2675_ = lean_nat_sub(v___x_2645_, v___x_2655_);
                v___x_2676_ = l_Lean_FuzzyMatching_instInhabitedScore_default;
                v___x_2677_ = lean_nat_mul(v___x_2674_, v___x_2645_);
                crate::leanh::lean_dec(v___x_2674_);
                v___x_2678_ = lean_nat_mul(v___x_2677_, v___x_2647_);
                crate::leanh::lean_dec(v___x_2677_);
                v___x_2679_ = lean_nat_mul(v___x_2675_, v___x_2647_);
                crate::leanh::lean_dec(v___x_2675_);
                v___x_2680_ = lean_nat_add(v___x_2678_, v___x_2679_);
                crate::leanh::lean_dec(v___x_2679_);
                crate::leanh::lean_dec(v___x_2678_);
                v___x_2681_ = crate::leanh::lean_box((v___x_2676_) as usize);
                v___x_2682_ = lean_array_get(v___x_2681_, v_fst_2673_, v___x_2680_);
                crate::leanh::lean_dec(v___x_2681_);
                v___x_2683_ = lean_nat_add(v___x_2680_, v___x_2655_);
                crate::leanh::lean_dec(v___x_2680_);
                v___x_2684_ = crate::leanh::lean_box((v___x_2676_) as usize);
                v___x_2685_ = lean_array_get(v___x_2684_, v_fst_2673_, v___x_2683_);
                crate::leanh::lean_dec(v___x_2683_);
                crate::leanh::lean_dec(v_fst_2673_);
                crate::leanh::lean_dec(v___x_2684_);
                v___x_2686_ = (crate::leanh::lean_unbox(v___x_2682_) as u16);
                v___x_2687_ = (crate::leanh::lean_unbox(v___x_2685_) as u16);
                v___x_2688_ = lean_int16_dec_le(v___x_2686_, v___x_2687_);
                if v___x_2688_ == 0 {
                    crate::leanh::lean_dec(v___x_2685_);
                    v___x_2689_ = (crate::leanh::lean_unbox(v___x_2682_) as u16);
                    crate::leanh::lean_dec(v___x_2682_);
                    v___y_2638_ = v___x_2689_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2682_);
                    v___x_2690_ = (crate::leanh::lean_unbox(v___x_2685_) as u16);
                    crate::leanh::lean_dec(v___x_2685_);
                    v___y_2638_ = v___x_2690_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore___boxed(
    mut v_pattern_2694_: *mut crate::leanh::LeanObject,
    mut v_word_2695_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2696_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2698_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(
        v_pattern_2694_,
        v_word_2695_,
        v_patternRoles_2696_,
        v_wordRoles_2697_,
    );
    crate::leanh::lean_dec_ref(v_wordRoles_2697_);
    crate::leanh::lean_dec_ref(v_patternRoles_2696_);
    crate::leanh::lean_dec_ref(v_word_2695_);
    crate::leanh::lean_dec_ref(v_pattern_2694_);
    return v_res_2698_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(
    mut v_wordRoles_2699_: *mut crate::leanh::LeanObject,
    mut v_range_2700_: *mut crate::leanh::LeanObject,
    mut v_b_2701_: *mut crate::leanh::LeanObject,
    mut v_i_2702_: *mut crate::leanh::LeanObject,
    mut v_hs_2703_: *mut crate::leanh::LeanObject,
    mut v_hl_2704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2705_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___redArg(v_wordRoles_2699_, v_range_2700_, v_b_2701_, v_i_2702_);
    return v___x_2705_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0___boxed(
    mut v_wordRoles_2706_: *mut crate::leanh::LeanObject,
    mut v_range_2707_: *mut crate::leanh::LeanObject,
    mut v_b_2708_: *mut crate::leanh::LeanObject,
    mut v_i_2709_: *mut crate::leanh::LeanObject,
    mut v_hs_2710_: *mut crate::leanh::LeanObject,
    mut v_hl_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2712_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__0(v_wordRoles_2706_, v_range_2707_, v_b_2708_, v_i_2709_, v_hs_2710_, v_hl_2711_);
    crate::leanh::lean_dec_ref(v_range_2707_);
    crate::leanh::lean_dec_ref(v_wordRoles_2706_);
    return v_res_2712_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(
    mut v_word_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_pattern_2715_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2716_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2717_: *mut crate::leanh::LeanObject,
    mut v___x_2718_: *mut crate::leanh::LeanObject,
    mut v___x_2719_: *mut crate::leanh::LeanObject,
    mut v_range_2720_: *mut crate::leanh::LeanObject,
    mut v_b_2721_: *mut crate::leanh::LeanObject,
    mut v_i_2722_: *mut crate::leanh::LeanObject,
    mut v_hs_2723_: *mut crate::leanh::LeanObject,
    mut v_hl_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___redArg(v_word_2713_, v_a_2714_, v_pattern_2715_, v_patternRoles_2716_, v_wordRoles_2717_, v___x_2718_, v___x_2719_, v_range_2720_, v_b_2721_, v_i_2722_);
    return v___x_2725_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5___boxed(
    mut v_word_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_pattern_2728_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2729_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2730_: *mut crate::leanh::LeanObject,
    mut v___x_2731_: *mut crate::leanh::LeanObject,
    mut v___x_2732_: *mut crate::leanh::LeanObject,
    mut v_range_2733_: *mut crate::leanh::LeanObject,
    mut v_b_2734_: *mut crate::leanh::LeanObject,
    mut v_i_2735_: *mut crate::leanh::LeanObject,
    mut v_hs_2736_: *mut crate::leanh::LeanObject,
    mut v_hl_2737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2738_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__5(v_word_2726_, v_a_2727_, v_pattern_2728_, v_patternRoles_2729_, v_wordRoles_2730_, v___x_2731_, v___x_2732_, v_range_2733_, v_b_2734_, v_i_2735_, v_hs_2736_, v_hl_2737_);
    crate::leanh::lean_dec_ref(v_range_2733_);
    crate::leanh::lean_dec(v___x_2732_);
    crate::leanh::lean_dec_ref(v___x_2731_);
    crate::leanh::lean_dec_ref(v_wordRoles_2730_);
    crate::leanh::lean_dec_ref(v_patternRoles_2729_);
    crate::leanh::lean_dec_ref(v_pattern_2728_);
    crate::leanh::lean_dec(v_a_2727_);
    crate::leanh::lean_dec_ref(v_word_2726_);
    return v_res_2738_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(
    mut v_word_2739_: *mut crate::leanh::LeanObject,
    mut v_pattern_2740_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2741_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2742_: *mut crate::leanh::LeanObject,
    mut v___x_2743_: *mut crate::leanh::LeanObject,
    mut v___x_2744_: *mut crate::leanh::LeanObject,
    mut v___x_2745_: *mut crate::leanh::LeanObject,
    mut v___x_2746_: *mut crate::leanh::LeanObject,
    mut v_range_2747_: *mut crate::leanh::LeanObject,
    mut v_b_2748_: *mut crate::leanh::LeanObject,
    mut v_i_2749_: *mut crate::leanh::LeanObject,
    mut v_hs_2750_: *mut crate::leanh::LeanObject,
    mut v_hl_2751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___redArg(v_word_2739_, v_pattern_2740_, v_patternRoles_2741_, v_wordRoles_2742_, v___x_2743_, v___x_2744_, v___x_2745_, v___x_2746_, v_range_2747_, v_b_2748_, v_i_2749_);
    return v___x_2752_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6___boxed(
    mut v_word_2753_: *mut crate::leanh::LeanObject,
    mut v_pattern_2754_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2755_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2756_: *mut crate::leanh::LeanObject,
    mut v___x_2757_: *mut crate::leanh::LeanObject,
    mut v___x_2758_: *mut crate::leanh::LeanObject,
    mut v___x_2759_: *mut crate::leanh::LeanObject,
    mut v___x_2760_: *mut crate::leanh::LeanObject,
    mut v_range_2761_: *mut crate::leanh::LeanObject,
    mut v_b_2762_: *mut crate::leanh::LeanObject,
    mut v_i_2763_: *mut crate::leanh::LeanObject,
    mut v_hs_2764_: *mut crate::leanh::LeanObject,
    mut v_hl_2765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2766_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6(v_word_2753_, v_pattern_2754_, v_patternRoles_2755_, v_wordRoles_2756_, v___x_2757_, v___x_2758_, v___x_2759_, v___x_2760_, v_range_2761_, v_b_2762_, v_i_2763_, v_hs_2764_, v_hl_2765_);
    crate::leanh::lean_dec_ref(v_range_2761_);
    crate::leanh::lean_dec(v___x_2760_);
    crate::leanh::lean_dec(v___x_2759_);
    crate::leanh::lean_dec(v___x_2758_);
    crate::leanh::lean_dec_ref(v___x_2757_);
    crate::leanh::lean_dec_ref(v_wordRoles_2756_);
    crate::leanh::lean_dec_ref(v_patternRoles_2755_);
    crate::leanh::lean_dec_ref(v_pattern_2754_);
    crate::leanh::lean_dec_ref(v_word_2753_);
    return v_res_2766_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(
    mut v___x_2767_: *mut crate::leanh::LeanObject,
    mut v___x_2768_: *mut crate::leanh::LeanObject,
    mut v_word_2769_: *mut crate::leanh::LeanObject,
    mut v_pattern_2770_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2771_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2772_: *mut crate::leanh::LeanObject,
    mut v___x_2773_: *mut crate::leanh::LeanObject,
    mut v___x_2774_: *mut crate::leanh::LeanObject,
    mut v_range_2775_: *mut crate::leanh::LeanObject,
    mut v_b_2776_: *mut crate::leanh::LeanObject,
    mut v_i_2777_: *mut crate::leanh::LeanObject,
    mut v_hs_2778_: *mut crate::leanh::LeanObject,
    mut v_hl_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2780_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___redArg(v___x_2767_, v___x_2768_, v_word_2769_, v_pattern_2770_, v_patternRoles_2771_, v_wordRoles_2772_, v___x_2773_, v___x_2774_, v_range_2775_, v_b_2776_, v_i_2777_);
    return v___x_2780_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6___boxed(
    mut v___x_2781_: *mut crate::leanh::LeanObject,
    mut v___x_2782_: *mut crate::leanh::LeanObject,
    mut v_word_2783_: *mut crate::leanh::LeanObject,
    mut v_pattern_2784_: *mut crate::leanh::LeanObject,
    mut v_patternRoles_2785_: *mut crate::leanh::LeanObject,
    mut v_wordRoles_2786_: *mut crate::leanh::LeanObject,
    mut v___x_2787_: *mut crate::leanh::LeanObject,
    mut v___x_2788_: *mut crate::leanh::LeanObject,
    mut v_range_2789_: *mut crate::leanh::LeanObject,
    mut v_b_2790_: *mut crate::leanh::LeanObject,
    mut v_i_2791_: *mut crate::leanh::LeanObject,
    mut v_hs_2792_: *mut crate::leanh::LeanObject,
    mut v_hl_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2794_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore_spec__6_spec__6(v___x_2781_, v___x_2782_, v_word_2783_, v_pattern_2784_, v_patternRoles_2785_, v_wordRoles_2786_, v___x_2787_, v___x_2788_, v_range_2789_, v_b_2790_, v_i_2791_, v_hs_2792_, v_hl_2793_);
    crate::leanh::lean_dec_ref(v_range_2789_);
    crate::leanh::lean_dec(v___x_2788_);
    crate::leanh::lean_dec_ref(v___x_2787_);
    crate::leanh::lean_dec_ref(v_wordRoles_2786_);
    crate::leanh::lean_dec_ref(v_patternRoles_2785_);
    crate::leanh::lean_dec_ref(v_pattern_2784_);
    crate::leanh::lean_dec_ref(v_word_2783_);
    crate::leanh::lean_dec(v___x_2782_);
    crate::leanh::lean_dec(v___x_2781_);
    return v_res_2794_;
}
pub unsafe fn l_Nat_cast___at___00Lean_FuzzyMatching_fuzzyMatchScore_x3f_spec__0(
    mut v_a_2795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2796_ = lean_nat_to_int(v_a_2795_);
    return v___x_2796_;
}
pub unsafe fn _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0() -> f64 {
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: f64 = 0.0;
    v___x_2797_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2798_ = lean_float_of_nat(v___x_2797_);
    return v___x_2798_;
}
pub unsafe fn _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1() -> f64 {
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: f64 = 0.0;
    v___x_2799_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2800_ = lean_float_of_nat(v___x_2799_);
    return v___x_2800_;
}
pub unsafe fn _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2801_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2802_ = lean_nat_to_int(v___x_2801_);
    return v___x_2802_;
}
pub unsafe fn _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2803_: f64 = 0.0;
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2803_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0),
        core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once),
        _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0,
    );
    v___x_2804_ = crate::leanh::lean_box_float(v___x_2803_);
    return v___x_2804_;
}
pub unsafe fn _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2805_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1;
    v___x_2806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2806_, 0, v___x_2805_);
    return v___x_2806_;
}
pub unsafe fn l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(
    mut v_pattern_2807_: *mut crate::leanh::LeanObject,
    mut v_word_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2810_: f64 = 0.0;
    let mut v___y_2811_: f64 = 0.0;
    let mut v___x_2812_: u8 = 0;
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: u8 = 0;
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_score_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_perfect_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_perfectMatch_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: f64 = 0.0;
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: f64 = 0.0;
    let mut v_normScore_2835_: f64 = 0.0;
    let mut v___x_2836_: f64 = 0.0;
    let mut v___x_2837_: f64 = 0.0;
    let mut v___x_2838_: u8 = 0;
    let mut v___x_2839_: u8 = 0;
    let mut v___x_2840_: u8 = 0;
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: u8 = 0;
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_score_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2817_ = lean_string_utf8_byte_size(v_pattern_2807_);
                v___x_2818_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2819_ = lean_nat_dec_eq(v___x_2817_, v___x_2818_);
                if v___x_2819_ == 0 {
                    v___x_2820_ = lean_string_length(v_word_2808_);
                    v___x_2821_ = lean_string_length(v_pattern_2807_);
                    v___x_2839_ = lean_nat_dec_lt(v___x_2820_, v___x_2821_);
                    if v___x_2839_ == 0 {
                        v___x_2840_ = l_String_charactersIn(v_pattern_2807_, v_word_2808_);
                        if v___x_2840_ == 0 {
                            v___x_2841_ = crate::leanh::lean_box(0);
                            return v___x_2841_;
                        } else {
                            if v___x_2819_ == 0 {
                                v___x_2842_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_pattern_2807_);
                                v___x_2843_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_iterateLookaround___at___00__private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_stringInfo_spec__0(v_word_2808_);
                                v___x_2844_ = l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_fuzzyMatchCore(v_pattern_2807_, v_word_2808_, v___x_2842_, v___x_2843_);
                                crate::leanh::lean_dec_ref(v___x_2843_);
                                crate::leanh::lean_dec_ref(v___x_2842_);
                                if crate::leanh::lean_obj_tag(v___x_2844_) == 1 {
                                    v_val_2845_ = crate::leanh::lean_ctor_get(v___x_2844_, 0);
                                    crate::leanh::lean_inc(v_val_2845_);
                                    crate::leanh::lean_dec_ref_known(v___x_2844_, 1);
                                    v___x_2846_ = lean_nat_dec_eq(v___x_2821_, v___x_2820_);
                                    if v___x_2846_ == 0 {
                                        v_score_2823_ = v_val_2845_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_2847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2), core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2_once), _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__2);
                                        v_score_2848_ = lean_int_mul(v_val_2845_, v___x_2847_);
                                        crate::leanh::lean_dec(v_val_2845_);
                                        v_score_2823_ = v_score_2848_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2844_);
                                    v___x_2849_ = crate::leanh::lean_box(0);
                                    return v___x_2849_;
                                }
                            } else {
                                v___x_2850_ = crate::leanh::lean_box(0);
                                return v___x_2850_;
                            }
                        }
                    } else {
                        v___x_2851_ = crate::leanh::lean_box(0);
                        return v___x_2851_;
                    }
                } else {
                    v___x_2852_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3_once
                        ),
                        _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3,
                    );
                    return v___x_2852_;
                }
            }
            1 => {
                v___x_2812_ = lean_float_decLe(v___y_2810_, v___y_2811_);
                if v___x_2812_ == 0 {
                    v___x_2813_ = crate::leanh::lean_box_float(v___y_2811_);
                    v___x_2814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2814_, 0, v___x_2813_);
                    return v___x_2814_;
                } else {
                    v___x_2815_ = crate::leanh::lean_box_float(v___y_2810_);
                    v___x_2816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2816_, 0, v___x_2815_);
                    return v___x_2816_;
                }
            }
            2 => {
                v_perfect_2824_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2825_ = lean_nat_mul(v_perfect_2824_, v___x_2821_);
                v___x_2826_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2827_ = lean_nat_add(v___x_2821_, v___x_2826_);
                v___x_2828_ = lean_nat_mul(v___x_2821_, v___x_2827_);
                crate::leanh::lean_dec(v___x_2827_);
                v___x_2829_ = lean_nat_shiftr(v___x_2828_, v___x_2826_);
                crate::leanh::lean_dec(v___x_2828_);
                v___x_2830_ = lean_nat_sub(v___x_2829_, v___x_2826_);
                crate::leanh::lean_dec(v___x_2829_);
                v_perfectMatch_2831_ = lean_nat_add(v___x_2825_, v___x_2830_);
                crate::leanh::lean_dec(v___x_2830_);
                crate::leanh::lean_dec(v___x_2825_);
                v___x_2832_ = l_Float_ofInt(v_score_2823_);
                crate::leanh::lean_dec(v_score_2823_);
                v___x_2833_ = lean_nat_to_int(v_perfectMatch_2831_);
                v___x_2834_ = l_Float_ofInt(v___x_2833_);
                crate::leanh::lean_dec(v___x_2833_);
                v_normScore_2835_ = lean_float_div(v___x_2832_, v___x_2834_);
                v___x_2836_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0_once
                    ),
                    _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__0,
                );
                v___x_2837_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1_once
                    ),
                    _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__1,
                );
                v___x_2838_ = lean_float_decLe(v___x_2837_, v_normScore_2835_);
                if v___x_2838_ == 0 {
                    v___y_2810_ = v___x_2836_;
                    v___y_2811_ = v___x_2837_;
                    state = 1;
                    continue;
                } else {
                    v___y_2810_ = v___x_2836_;
                    v___y_2811_ = v_normScore_2835_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___boxed(
    mut v_pattern_2853_: *mut crate::leanh::LeanObject,
    mut v_word_2854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2855_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_2853_, v_word_2854_);
    crate::leanh::lean_dec_ref(v_word_2854_);
    crate::leanh::lean_dec_ref(v_pattern_2853_);
    return v_res_2855_;
}
pub unsafe fn l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(
    mut v_pattern_2856_: *mut crate::leanh::LeanObject,
    mut v_word_2857_: *mut crate::leanh::LeanObject,
    mut v_threshold_2858_: f64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2859_ = l_Lean_FuzzyMatching_fuzzyMatchScore_x3f(v_pattern_2856_, v_word_2857_);
    if crate::leanh::lean_obj_tag(v___x_2859_) == 0 {
        return v___x_2859_;
    } else {
        let mut v_val_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2861_: f64 = 0.0;
        let mut v___x_2862_: u8 = 0;
        v_val_2860_ = crate::leanh::lean_ctor_get(v___x_2859_, 0);
        crate::leanh::lean_inc(v_val_2860_);
        v___x_2861_ = crate::leanh::lean_unbox_float(v_val_2860_);
        crate::leanh::lean_dec(v_val_2860_);
        v___x_2862_ = lean_float_decLt(v_threshold_2858_, v___x_2861_);
        if v___x_2862_ == 0 {
            let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2859_, 1);
            v___x_2863_ = crate::leanh::lean_box(0);
            return v___x_2863_;
        } else {
            return v___x_2859_;
        }
    }
}
pub unsafe fn l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f___boxed(
    mut v_pattern_2864_: *mut crate::leanh::LeanObject,
    mut v_word_2865_: *mut crate::leanh::LeanObject,
    mut v_threshold_2866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_threshold_boxed_2867_: f64 = 0.0;
    let mut v_res_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_threshold_boxed_2867_ = crate::leanh::lean_unbox_float(v_threshold_2866_);
    crate::leanh::lean_dec_ref(v_threshold_2866_);
    v_res_2868_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(
        v_pattern_2864_,
        v_word_2865_,
        v_threshold_boxed_2867_,
    );
    crate::leanh::lean_dec_ref(v_word_2865_);
    crate::leanh::lean_dec_ref(v_pattern_2864_);
    return v_res_2868_;
}
pub unsafe fn l_Lean_FuzzyMatching_fuzzyMatch(
    mut v_pattern_2869_: *mut crate::leanh::LeanObject,
    mut v_word_2870_: *mut crate::leanh::LeanObject,
    mut v_threshold_2871_: f64,
) -> u8 {
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(
        v_pattern_2869_,
        v_word_2870_,
        v_threshold_2871_,
    );
    if crate::leanh::lean_obj_tag(v___x_2872_) == 0 {
        let mut v___x_2873_: u8 = 0;
        v___x_2873_ = 0;
        return v___x_2873_;
    } else {
        let mut v___x_2874_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_2872_, 1);
        v___x_2874_ = 1;
        return v___x_2874_;
    }
}
pub unsafe fn l_Lean_FuzzyMatching_fuzzyMatch___boxed(
    mut v_pattern_2875_: *mut crate::leanh::LeanObject,
    mut v_word_2876_: *mut crate::leanh::LeanObject,
    mut v_threshold_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_threshold_boxed_2878_: f64 = 0.0;
    let mut v_res_2879_: u8 = 0;
    let mut v_r_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_threshold_boxed_2878_ = crate::leanh::lean_unbox_float(v_threshold_2877_);
    crate::leanh::lean_dec_ref(v_threshold_2877_);
    v_res_2879_ =
        l_Lean_FuzzyMatching_fuzzyMatch(v_pattern_2875_, v_word_2876_, v_threshold_boxed_2878_);
    crate::leanh::lean_dec_ref(v_word_2876_);
    crate::leanh::lean_dec_ref(v_pattern_2875_);
    v_r_2880_ = crate::leanh::lean_box((v_res_2879_) as usize);
    return v_r_2880_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_FuzzyMatching(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_OfScientific(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_CompletionUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_FuzzyMatching_instInhabitedCharRole_default =
        _init_l_Lean_FuzzyMatching_instInhabitedCharRole_default();
    l_Lean_FuzzyMatching_instInhabitedCharRole = _init_l_Lean_FuzzyMatching_instInhabitedCharRole();
    l_Lean_FuzzyMatching_instInhabitedScore_default =
        _init_l_Lean_FuzzyMatching_instInhabitedScore_default();
    l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore =
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_instInhabitedScore();
    l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful =
        _init_l___private_Lean_Data_FuzzyMatching_0__Lean_FuzzyMatching_Score_awful();
    l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1 =
        _init_l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l_Lean_FuzzyMatching_fuzzyMatchScore_x3f___closed__3___boxed__const__1,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_FuzzyMatching(
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
pub unsafe fn initialize_Lean_Data_FuzzyMatching(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_OfScientific(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_Completion_CompletionUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_FuzzyMatching(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_FuzzyMatching(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_FuzzyMatching(builtin);
}
